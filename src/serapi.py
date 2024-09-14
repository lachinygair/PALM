import sys
from .re_patterns import *
import pexpect
from pexpect.popen_spawn import PopenSpawn
import signal
from itertools import chain
import sexpdata
from sexpdata import Symbol
from .utils import *
from .config import opam_path


class CoqExn(Exception):

    def __init__(self, err_msg):
        super().__init__()
        self.err_msg = err_msg

    def __str__(self):
        return self.err_msg


    def __repr__(self):
        return str(self)


class CoqTimeout(Exception):
    def __str__(self):
        return 'CoqTimeout'


def log(msg, msg_type='INFO'):
  if msg_type == 'INFO':
    prefix = ''
  elif msg_type == 'WARNING':
    prefix = '\033[33mWARNING: '
  elif msg_type == 'ERROR':
    prefix = '\033[91mERROR: '
  suffix = '\033[0m'
  print(prefix + str(msg) + suffix)


def escape(vernac_cmd):
    return vernac_cmd.replace('\\', '\\\\').replace('"', '\\"')


def symbol2str(s):
    return s.value() if isinstance(s, Symbol) else str(s)


def print_mod_path(modpath):
    if modpath[0] == Symbol('MPdot'):
        return print_mod_path(modpath[1]) + '.' + symbol2str(modpath[2][1])
    elif modpath[0] == Symbol('MPfile'):
        return '.'.join([symbol2str(x[1]) for x in modpath[1][1]][::-1])
    else: 
        assert modpath[0] == Symbol('MPbound')
        return '.'.join([symbol2str(x[1]) for x in modpath[1][2][1]][::-1] + [symbol2str(modpath[1][1][1])])


def mod_path_file(modpath):
    if modpath[0] == Symbol('MPdot'):
        return mod_path_file(modpath[1])
    elif modpath[0] == Symbol('MPfile'):
        return '.'.join([symbol2str(x[1]) for x in modpath[1][1]][::-1])
    else:
        assert modpath[0] == Symbol('MPbound')
        return ''
    

def byte_index_to_char_index(s, byte_index):
    byte_seq = s.encode('utf-8')
    char_count = 0
    for i in range(byte_index):
        if (byte_seq[i] & 0xC0) != 0x80:
            char_count += 1
    return char_count


class SerAPI:
    encoding = 'utf-8'
    def __init__(self, timeout, version, options='', debug=False):
        'Initialize the SerAPI subprocess'
        self.debug = debug
        # try:
            # --omit_loc
        print(os.path.join(opam_path, version, 'bin/sertop') + ' --implicit --print0 ' + options)
        self.proc = PopenSpawn(os.path.join(opam_path, version, 'bin/sertop') + ' --implicit --print0 ' + options, encoding=SerAPI.encoding, timeout=timeout, maxread=10000000)
        # except FileNotFoundError:
        #     log('Please make sure the "sertop" program is in the PATH.\nYou may have to run "eval $(opam env)".', 'ERROR')
        #     sys.exit(1)
        self.proc.expect_exact('(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))\0')
        self.send('Noop')
        self.states_stack = []

        # global printing options
        # self.add_and_execute('Unset Printing Notations.')
        # self.add_and_execute('Unset Printing Wildcard.')
        # self.add_and_execute('Set Printing Coercions.')
        # self.add_and_execute('Unset Printing Allow Match Default Clause.')
        # self.add_and_execute('Unset Printing Factorizable Match Patterns.')
        # self.add_and_execute('Unset Printing Compact Contexts.')
        # self.add_and_execute('Set Printing Implicit.')
        # self.add_and_execute('Set Printing Depth 999999.')
        # self.add_and_execute('Unset Printing Records.')

        # initialize the state stack
        self.push()
  
        self.ast_cache = {}
        self.dead = False


    def set_timeout(self, timeout):
        self.proc.timeout = timeout


    def get_timeout(self):
        return self.proc.timeout
    

    def ctr_c(self):
        self.proc.kill(signal.SIGINT) 
        self.proc.expect(['\(Answer \d+ Ack\)\x00.*\(Answer \d+ Completed\)\x00',
                              '\(Answer \d+ Ack\)\x00.*\(Answer \d+\(CoqExn.*\)\x00'])
        self.send('Noop')

    def send(self, cmd, report_exception=True, timeout=-1):
        'Send a command to SerAPI and retrieve the responses'
        assert '\n' not in cmd
        self.proc.sendline(cmd)
        try:
            self.proc.expect(['\(Answer \d+ Ack\)\x00.*\(Answer \d+ Completed\)\x00',
                              '\(Answer \d+ Ack\)\x00.*\(Answer \d+\(CoqExn.*\)\x00'], timeout=timeout)
        except pexpect.TIMEOUT as ex:
            print(self.proc.before)
            raise CoqTimeout
        except pexpect.exceptions.EOF as eof:
            raise CoqExn(str(eof))
        raw_responses = self.proc.after
        ack_num = int(re.search(r'^\(Answer (?P<num>\d+)', raw_responses)['num'])
        for num in re.findall(r'(?<=\(Answer) \d+', raw_responses):
            assert int(num) == ack_num
        responses = []
        for item in raw_responses.split('\x00'):
            item = item.strip()
            if item == '':
                continue
            if not item.startswith('(Feedback') and not item.startswith('(Answer'):
                m = re.search(r'\(Feedback|\(Answer', item)
                if m is None:
                    continue
                item = item[m.span()[0]:]
                assert item.endswith(')')
            parsed_item = sexpdata.loads(item, nil=None, true=None)
            if 'CoqExn' in item and report_exception:  # an error occured in Coq
                assert parsed_item[2][0] == Symbol('CoqExn')
                msg = sexpdata.dumps(parsed_item[2][1][5])[6:-2]
                raise CoqExn(msg)
            responses.append(parsed_item)
        return responses, raw_responses


    def send_add(self, cmd, report_exception=True):
        'Send a (Add () "XXX") command to SerAPI, return the state id and optionally the AST'
        responses, raw_responses = self.send('(Add () "%s")' % escape(cmd), report_exception)
        state_ids = [int(sid) for sid in ADDED_STATE_PATTERN.findall(raw_responses)]
        return state_ids, responses


    def query_ast(self, cmd):
        'Query the AST of the vernac command just added'
        responses, _ = self.send('(Parse () "%s")' % escape(cmd))
        ast = responses[1][2][1][0]
        assert ast[0] == Symbol('CoqAst')
        return ast


    def query_library(self, lib):
        responses, _ = self.send('(Query () (LocateLibrary "%s"))' % lib)
        physical_path = symbol2str(responses[1][2][1][0][3])
        return physical_path
    
    def locate(self, term: str):
        succ, responses = self.add_and_execute_once('Locate %s.' % term)
        if not succ:
            return None
        responses = responses[3][1][3][1][4][1]
        if responses.startswith('No object of basename'):
            return None
        # rs = [r for r in responses.split('\n')]
        rs = []
        for r in responses.split('\n'):
            if '(' in r:
                r = r[:r.find('(')]
            if not all(c.isspace() or c == '\n' for c in r):
                rs.append(r)

        if len(rs) > 1 and rs[1].startswith('  '):
            return rs[0] + ' ' + rs[1].strip()
        return rs[0]


    def query_qualid(self, qualid):
        try:
            responses, _ = self.send('(Query () (Locate "%s"))' % qualid)
            if responses[1][2][1] == [] and qualid.startswith('SerTop.'):
                qualid = qualid[len('SerTop.'):]
                responses, _ = self.send('(Query () (Locate "%s"))' % qualid)
            # assert len(responses[1][2][1]) == 1
            if responses[1][2][1] == []:
                return None
            short_responses = responses[1][2][1][0][1][0][1]
            assert short_responses[1][0] == Symbol('DirPath')
            short_ident = '.'.join([symbol2str(x[1]) for x in short_responses[1][1][::-1]] + [symbol2str(short_responses[2][1])])
            return short_ident
        except CoqExn as e:
            return None


    def query_env(self):
        'Query the global environment'
        responses, _ = self.send('(Query () Env)')
        env = responses[1][2][1][0]

        # store the constants
        constants = []
        for const in env[1][0][1][0][1]:
            # identifier
            qualid = print_mod_path(const[0][1]) + '.' + symbol2str(const[0][2][1])
            short_ident = self.query_qualid(qualid)
            # term
            assert const[1][0][1][0] == Symbol('const_body')
            if const[1][0][1][1][0] == Symbol('Undef'):  # delaration
                opaque = None
                term = None
            elif const[1][0][1][1][0] == Symbol('Def'):  # transparent definition
                opaque = False
                term = None
            else:
                assert const[1][0][1][1][0] == Symbol('OpaqueDef')  # opaque definition
                opaque = True
                term = None
            # type
            assert const[1][0][2][0] == Symbol('const_type')
            type_sexp = sexpdata.dumps(const[1][0][2][1])
            type = self.print_constr(type_sexp)
            sort = self.query_type(type_sexp, return_str=True)
            constants.append({'short_ident': short_ident, 'qualid': qualid, 'term': term, 
                              'type': type, 'sort': sort, 'opaque': opaque})

        # store the inductives
        inductives = []
        for induct in env[1][0][1][1][1]:
            # identifier
            qualid = print_mod_path(induct[0][1]) + '.' + symbol2str(induct[0][2][1])
            short_ident = self.query_qualid(qualid)
            if qualid.startswith('SerTop.'):
                logical_path = 'SerTop'
            else:
                logical_path = mod_path_file(induct[0][1])
            assert qualid.startswith(logical_path)
            # blocks
            blocks = []
            for blk in induct[1][0][0][1]:
                blk_qualid = '.'.join(qualid.split('.')[:-1] + [symbol2str(blk[0][1][1])])
                blk_short_ident = self.query_qualid(blk_qualid)
                # constructors
                constructors = []
                for c_name, c_type in zip(blk[3][1], blk[4][1]):
                    c_name = symbol2str(c_name[1])
                    c_type = self.print_constr(sexpdata.dumps(c_type))
                    constructors.append((c_name, c_type))
                blocks.append({'short_ident': blk_short_ident, 'qualid': blk_qualid, 'constructors': constructors})

            inductives.append({'blocks': blocks, 'is_record': induct[1][0][1][1] != Symbol('NotRecord'), 'sexp': sexpdata.dumps(induct)})

        return constants, inductives


    def query_goals(self):
        'Retrieve a list of open goals'
        responses, _ = self.send('(Query () Goals)')
        assert responses[1][2][0] == Symbol('ObjList')
        if responses[1][2][1] == []:  #  no goals
            return [], [], [], []
        else:
            assert len(responses[1][2][1]) == 1
            def store_goals(goals_sexp):
                goals = []
                for g in goals_sexp:
                    hypotheses = []
                    for h in g[2][1]:
                        h_sexp = sexpdata.dumps(h[2])
                        hypotheses.append({'idents': [symbol2str(ident[1]) for ident in h[0][::-1]], 
                                           'term': [None if t == [] else self.print_constr(sexpdata.dumps(t)) for t in h[1]],
                                           'type': self.print_constr(h_sexp)
                                           }) 
                    
                    type_sexp = sexpdata.dumps(g[1][1])
                    goals.append({'type': self.print_constr(type_sexp),
                                  'hypotheses': hypotheses[::-1]})
                return goals
            fg_goals = store_goals(responses[1][2][1][0][1][0][1])
            bg_goals = store_goals(list(chain.from_iterable(chain.from_iterable(responses[1][2][1][0][1][1][1]))))
            shelved_goals = store_goals(responses[1][2][1][0][1][2][1])
            given_up_goals = store_goals(responses[1][2][1][0][1][3][1])
            return fg_goals, bg_goals, shelved_goals, given_up_goals
    

    def query_all_goals_pretty(self):
        def extract_goals(goals):
            res = []
            for goal in goals:
                tmp = {'goal': goal['type'], 'hypos': {}}
                for h in goal['hypotheses']:
                    for id in h['idents']:
                        tmp['hypos'][id] = h['type']
                res.append(tmp)
            return res
        
        fg_goals, bg_goals, shelved_goals, _ = self.query_goals()
        fg_goals = extract_goals(fg_goals)
        bg_goals = extract_goals(bg_goals)
        shelved_goals = extract_goals(shelved_goals)

        return fg_goals, bg_goals, shelved_goals
    

    def query_goals_pretty(self):
        responses, _ = self.send('(Query ((pp ((pp_format PpStr)))) Goals)')
        assert responses[1][2][0] == Symbol('ObjList')
        goals = responses[1][2][1][0][1]
        return goals
    

    def has_open_goals(self):
        responses, _ = self.send('(Query () Goals)')
        assert responses[1][2][0] == Symbol('ObjList')
        return responses[1][2][1] != []


    def print_constr(self, sexp_str):
        if not hasattr(self, 'constr_cache'):
            self.constr_cache = {}
        if sexp_str not in self.constr_cache:
            try:
                responses, _ = self.send('(Print ((pp ((pp_format PpStr)))) (CoqConstr %s))' % sexp_str)
                self.constr_cache[sexp_str] = normalize_spaces(symbol2str(responses[1][2][1][0][1]))
            except CoqExn as ex:
                if ex.err_msg == 'Not_found':
                    return None
                else:
                    raise ex
            except TypeError as ex:
                self.constr_cache[sexp_str] = normalize_spaces(symbol2str(responses[0][2][1][0][1]))
        return self.constr_cache[sexp_str]


    def query_vernac(self, cmd):
        return self.send('(Query () (Vernac "%s"))' % escape(cmd))


    def query_type(self, term_sexp, return_str=False):
        try:
            responses, _ = self.send('(Query () (Type %s))' % term_sexp)
        except CoqExn as ex:
            if ex.err_msg == 'Not_found':
                return None
            else:
                raise ex
        assert responses[1][2][1][0][0] == Symbol('CoqConstr')
        type_sexp = responses[1][2][1][0][1]
        if return_str:
            return self.print_constr(sexpdata.dumps(type_sexp))
        else:
            return type_sexp
        
    
    def print(self, term):
        succ, responses = self.add_and_execute_once('Print %s.' % term, timeout=5)
        if succ:
            res = responses[3][1][3][1][4][1]
            return normalize_spaces(res)
        else:
            return None
    

    def check(self, term):
        succ, responses = self.add_and_execute_once('Check %s.' % term, timeout=5)   
        if not succ:
            return None
        return normalize_spaces(responses[3][1][3][1][4][1])


    def search(self, term):
        _, responses = self.add_and_execute_once('Search _ %s.' % term)
        return [res[1][3][1][4][1] for res in responses[3:-2]]


    def add_and_execute(self, cmd):
        state_ids, _ = self.send_add(cmd)
        responses = self.execute(state_ids[-1])
        return state_ids, responses
    

    def execute(self, state_id, timeout=-1):
        cmd = '(Exec %d)' % state_id
        responses, _ = self.send(cmd, timeout=timeout)
        return responses
    

    def try_add_and_execute(self, cmd, timeout=-1):
        state_ids = []
        try:
            state_ids, _ = self.send_add(cmd)
            responses = self.execute(state_ids[-1], timeout=timeout)
            return state_ids, responses, None
        except CoqTimeout as e:
            print('try_add_and_execute err: ', str(e), cmd)
            self.ctr_c()
            if state_ids != []:
                self.cancel(state_ids)
            return [-1], '', str(e)
        except (CoqExn) as e:
            if state_ids is not []:
                self.cancel(state_ids)
            return [-1], '', str(e)
    

    def add_and_execute_once(self, cmd, timeout=-1):
        state_ids = []
        try:
            state_ids, _ = self.send_add(cmd)
            responses = self.execute(state_ids[-1], timeout=timeout)
            self.cancel(state_ids)
            return True, responses
        except CoqTimeout as e:
            print('add_and_execute_once err: ', str(e), cmd)
            self.ctr_c()
            if state_ids != []:
                self.cancel(state_ids)
            return False, str(e)
        except (CoqExn) as e:
            if state_ids != []:
                self.cancel(state_ids)
            return False, str(e)
        
    
    def parse(self, cmd: str):
        state_ids = []
        state_ids, responses = self.send_add(cmd, False)
        rs = []
        exn = ''
        end_ind = len(responses) - 1
        exn_ind = None
        while end_ind >= 0:
            tmp = responses[end_ind]
            if type(tmp[0]) is Symbol and sexpdata.dumps(tmp[0]) == 'Answer' and type(tmp[2]) is list \
                and type(tmp[2][0]) is Symbol and sexpdata.dumps(tmp[2][0]) == 'Added':
                break
            elif type(tmp[0]) is Symbol and sexpdata.dumps(tmp[0]) == 'Feedback':
                break
            elif type(tmp[2]) is list and type(tmp[2][0]) is Symbol and sexpdata.dumps(tmp[2][0]) == 'CoqExn':
                exn_ind = end_ind
            end_ind -= 1

        rs = responses[1 : end_ind + 1]
        if exn_ind is not None:
            exn = responses[exn_ind][2][1][3][1]
            exn = exn[1] if len(exn) > 1 else exn[0]
        sp = [(r[2][2][5][1], r[2][2][6][1]) for r in rs if sexpdata.dumps(r[0]) == 'Answer' and sexpdata.dumps(r[2][0]) == 'Added']
        codes = [cmd[byte_index_to_char_index(cmd, bp):byte_index_to_char_index(cmd, ep)] for bp, ep in sp]
        self.cancel(state_ids)
        return codes, exn
    

    def predict(self, k: int):
        succ, responses = self.add_and_execute_once('predict %d.' % k)
        if not succ:
            print(responses)
            return []
        res = responses[4][1][3][1][3][1][1]
        res = res.split(', ')
        return res
        

    def solve(self, tactic: str):
        # try:
        succ, responses = self.add_and_execute_once(tactic)
        # except Exception as e:
        #     print('err: ', e)
        #     return False, str(e)
        if not succ:
            return False, responses
        assert responses[-1][2] == Symbol('Completed')
        replace = responses[-3][1][3][1][3][1][1]
        if tactic.startswith('best'):
            msg = 'Replace the `best` tactic with:'
            assert replace.startswith(msg)
        elif tactic.startswith('hammer'):
            msg = 'Replace the hammer tactic with:'
            assert replace.startswith(msg)
        else:
            raise 'only best or hammer for automation, got ' + tactic
        replace = replace[len(msg):].strip()
        return True, replace


    def push(self):
        'push a new frame on the state stack (a checkpoint), which can be used to roll back to the current state'
        self.states_stack.append([])


    def cancel(self, states):
        self.send('(Cancel (%s))' % ' '.join([str(s) for s in states]))


    def pull(self):
        'remove a checkpoint created by push'
        states = self.states_stack.pop()
        self.states_stack[-1].extend(states)
        return len(states)


    def pop(self):
        'rollback to a checkpoint created by push'
        self.cancel(self.states_stack.pop())


    def pop_n(self, cnt):
        states = []
        for i in range(cnt):
            states.append(self.states_stack[-1].pop())
        self.cancel(states)


    def clean(self):
        self.proc.sendeof()
        self.proc.wait()
        self.dead = True

    def shutdown(self):
        self.proc.kill(signal.SIGKILL)
        self.dead = True

    def __enter__(self):
        return self


    def __exit__(self, exc_type, exc_value, traceback):
        self.clean()


if __name__ == '__main__':
    pass