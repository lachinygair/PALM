from .serapi import SerAPI
from .llm import LLM
from .proof_list import List
import re
from collections import deque
from .utils import *
from .retrieval import Retrieval
from .repair import Repair, WRONG_BULLET, UNFINISHED_BULLET, WRONG_BULLET_UNFOUCS, NO_MORE_GOALS, NO_MORE_SUBGOALS
from .config import *


replaces = [
    ('\n', ' '),
    ('Proof.', ''),
    ('proof.', ''),
    ('exact ', 'apply '),
    ('assumption.', 'auto.'),
    ('coq ', ''),
    ("`", ''),
    ("'''", ''),
    ('Qed.', ''),
    ("Qed'", ''),
    ('Qed', ''),
]


def tactic_unifier(serapi, tactic: str):
    tactic = tactic.replace('\n', ' ')
    tactic = normalize_spaces(tactic).strip()
    for replace in replaces:
        tactic = tactic.replace(replace[0], replace[1])
    if tactic.startswith('coq'):
        tactic = tactic[3:]
    if tactic.startswith('proof '):
        tactic = tactic[5:]
    if tactic.endswith('Qed'):
        tactic += '.'
    if 'Proof.' in tactic:
        tactic = tactic[tactic.find('Proof.')+6:]
    tactic = tactic.strip()
    parsed, exn = serapi.parse(tactic)
    return parsed, exn


class State:
    max_lemmas = 30
    max_defs = 25
    def __init__(self, serapi:SerAPI, llm:LLM, repair: Repair):
        self.success = False
        self.fg_goals = []
        self.bg_goals = []
        self.shelved_goals = []
        self.avoid = []
        self.structure = []
        self.history = List()
        self.original = ''
        self.llm = llm
        self.serapi = serapi
        self.fg_goals, self.bg_goals, self.shelved_goals = serapi.query_all_goals_pretty()
        # self.retrieval = Retrieval()
        self.repair = repair
        self.use_qualids = set()
        self.lemmas = []
        self.hammer_times = 0

    
    def reset(self):
        self.serapi = None; self.llm = None
    

    def append_avoid(self, to_avoid: str):
        self.avoid.append(to_avoid)


    # sauto simpl qsimpl ssimpl best
    def automation(self, tactic, depth=-1, use=[], time=-1):
        if depth > 0:
            tactic += ' depth: ' + str(depth)
        if len(use) > 0:
            tactic += ' use: ' + ','.join(use)
        if time > 0:
            tactic += ' time: ' + str(time)
        tactic = tactic if tactic.endswith('.') else tactic + '.'
        succ, res = self.serapi.solve(tactic)
        if not succ:
            # assert 'The `best` tactic failed' in str(res) or \
            #     'Hammer failed' in str(res), 'coq-hammer error: ' + str(res)
            return -1, res
        else:
            res = res + '.' if not res.endswith('.') else res
            res = res.replace('eauto', 'best')
            state_id, exn = self.execute_and_update(res, 'hammer')
            if state_id > 0 and exn is None and self.fg_goals != []:
                self.serapi.cancel([state_id])
                self.history.pop()
                state_id = -1
                exn = 'goal is not solved by hammer'
            return state_id, exn

        # return self.finish()
    

    def finish(self):
        if self.fg_goals + self.bg_goals + self.shelved_goals == []:
            return True
        else:
            return False
        # if self.fg_goals != []:
        #     return False
        # if self.bg_goals != []:
        #     self.execute_and_update(self.next_indicator())
        #     return False
        # if self.shelved_goals != []:
        #     return False

    
    def next_indicator(self, start=''):
        if start == '':
            start = self.structure[-1] if self.structure else '-'

        succ, response = self.serapi.add_and_execute_once(start)
        if succ:
            return start

        matches = re.search(WRONG_BULLET, response)
        if matches:
            _, res = matches.groups()
            return res
        matches = re.search(UNFINISHED_BULLET, response)
        if matches:
            _, cur = matches.groups()
            nx = next_indicator_litera(cur)
            while nx in self.structure:
                nx = next_indicator_litera(nx)
            return self.next_indicator(nx)
        matches = re.search(WRONG_BULLET_UNFOUCS, response)
        if matches:
            raise 'next_indicator error }'
            # _, unfocus = matches.groups()
            # return unfocus
        matches = re.search(NO_MORE_GOALS, response)
        if matches:
            return None
        matches = re.search(NO_MORE_SUBGOALS, response)
        if matches:
            return None
        raise 'next_indicator error'


    def get_premises(self):
        goals = self.fg_goals+self.bg_goals+self.shelved_goals
        return self.retrieval.retrieve_predict(self.serapi, goals)


    def query_llm(self, goals):
        premises, defs, lemmas = self.get_premises()
        self.lemmas = lemmas
        prompt = self.llm.get_prompt(goals, premises[:State.max_lemmas], defs)
        return self.llm.query(prompt.strip())


    def diff(self, fg_goals, bg_goals, shelved_goals):
        if not(len(self.fg_goals) == len(fg_goals)
               and len(self.bg_goals) == len(bg_goals)
               and len(self.shelved_goals) == len(shelved_goals)):
            return True
        
        for g1, g2 in zip(self.fg_goals+self.bg_goals+self.shelved_goals,
                          fg_goals+bg_goals+shelved_goals):
            if not (g1['goal'] == g2['goal'] and same_dict(g1['hypos'], g2['hypos'])):
                return True
        return False
        
        
    def execute_and_update(self, tactic: str, source=''):
        state_ids, response, exn = self.serapi.try_add_and_execute(tactic, timeout=1 if tactic.startswith('qsimpl') else -1)
        if state_ids == [-1]:
            return -1, exn
        
        res = state_ids[0]
        fg_goals, bg_goals, shelved_goals = self.serapi.query_all_goals_pretty()
        if self.diff(fg_goals, bg_goals, shelved_goals):
            self.fg_goals = fg_goals
            self.bg_goals = bg_goals
            self.shelved_goals = shelved_goals
            self.history.insert(tactic, state_ids[0], source)

            if is_indicator(tactic):
                if tactic in self.structure:
                    self.structure = self.structure[:self.structure.index(tactic)+1]
                else:
                    self.structure.append(tactic)
        else:
            self.serapi.cancel(state_ids)
            res = -1

        return res, None


    def prove(self, tactics_ori=''):
        if tactics_ori == '':
            tactics_ori = self.query_llm(self.fg_goals)
        
        self.original = tactics_ori
        tactics, exn = tactic_unifier(self.serapi, tactics_ori)
        print(tactics)
        if exn != '':
            print(exn, tactics_ori)
        tactics = deque([(t, '') for t in tactics])
        self.original = ' '.join([t[0] for t in tactics])
        while tactics:
            t, source = tactics[0]
            if t == '{':
                self.transform_curly(tactics)
                if not tactics:
                    return
                t, _ = tactics[0]
            print(t)
            state_id, exn = self.execute_and_update(t, source)
            # error happens
            if state_id < 0 and exn is not None:
                exn_msg = str(exn)
                print(t, exn_msg)
                repair_succ = self.repair.repair(exn_msg, self, tactics)
                if not repair_succ:
                    self.skip_goal(tactics)
            # success
            else:
                tactics.popleft()
                        
        if len(self.fg_goals) == 1:
            self.execute_and_update('shelve.')
        else:
            for fg_goal in self.fg_goals:
                self.execute_and_update(self.next_indicator())
                self.execute_and_update('shelve.')
        for bg_goal in self.bg_goals:
            self.execute_and_update(self.next_indicator())
            self.execute_and_update('shelve.')
        return self.finish()

    
    def skip_goal(self, tactics: deque):
        for t in tactics:
            assert type(t) is tuple and type(t[0]) is str
        while tactics:
            if tactics[0][0] in self.structure:
                break
            tactic, _ = tactics.popleft()
            qualids = extract_qualids(tactic)
            hypos = set(self.fg_goals[0]['hypos'].keys() if self.fg_goals != [] else [])
            for q in qualids:
                if q not in hypos and self.serapi.locate(q) is not None:
                    self.use_qualids.add(q)
    

    def backtrack(self):
        if not self.original:
            return False
        print('start backtrack')
        cur, bullets_cur = self.history.get_last_shelved()
        while cur:
            index = self.history.index(cur)
            self.focus(index)
            self.history.pop(index)
            self.hammer_times += 1
            succ = self.prove_with_hammer(strict=False)
            print('hammering: ', self.hammer_times, succ, bullets_cur)
            if succ:
                if self.finish():
                    return True
                index += 1
                print([n.tactic for n in self.history])
                while index < len(self.history):
                    tactic = self.history[index].tactic
                    print(index, tactic)
                    if is_indicator(tactic) and tactic in bullets_cur:
                        break
                    else:
                        self.history.pop(index)
                        index = self.history.cur + 1
                cur, bullets_cur = self.history.get_last_shelved()
            else:
                index -= 1
                while index >= 0 and self.history[index].tactic.startswith('qsimpl'):
                    self.history.pop(index)
                    index -= 1
                if index < 0:
                    return False
                cur = self.history[index]
                bullets_cur = self.history.get_structure(index)
                if is_indicator(cur.tactic):
                    self.history.cut_bullet(index)
                    cur = self.history[self.history.cur]
                    bullets_cur = self.history.get_structure(self.history.cur)
        self.focus(len(self.history))
        return self.finish()
    

    def prove_with_hammer(self, simpl=False, strict=True):
        if simpl:
            self.automation('ssimpl', use=self.use_qualids)
        state_id, exn = self.automation('best', 3, use=self.use_qualids)
        if not strict and state_id > 0 and exn is None:
            return True
        if state_id > 0 and exn is None \
            and self.fg_goals == [] and self.bg_goals == [] and self.shelved_goals == []:
            return True
        if self.use_qualids:
            state_id, exn = self.automation('best', 3)
            if not strict and state_id > 0 and exn is None:
                return True
            if state_id > 0 and exn is None \
                and self.fg_goals == [] and self.bg_goals == [] and self.shelved_goals == []:
                return True
        state_id, exn = self.automation('hammer')
        if not strict and state_id > 0 and exn is None:
            return True
        if state_id > 0 and exn is None and self.fg_goals == [] and self.bg_goals == [] and self.shelved_goals == []:
            return True
        print(exn)
        return False
    

    def focus(self, ind: int):
        print('focus: ', self.history.cur, ind)
        if self.history.cur == ind - 1:
            return
        if ind - 1 < self.history.cur:
            node = self.history[ind]
            self.serapi.cancel([node.state_id])
            self.history.cur = ind - 1
        else:
            for nd in self.history[self.history.cur + 1 : ind]:
                state_ids, _ = self.serapi.add_and_execute(nd.tactic)
                nd.state_id = state_ids[0]
            self.history.cur = ind - 1
        self.fg_goals, self.bg_goals, self.shelved_goals = self.serapi.query_all_goals_pretty()
        

    def transform_curly(self, tactics: deque):
        tactics.popleft()
        ts = []
        while tactics and tactics[0][0] != '}':
            t, _ = tactics.popleft()
            ts.append((t, 'transform_curly'))
        if not tactics:
            self.original = ''
            return
        tactics.popleft()
        # indicator = self.next_indicator()
        ts.reverse()
        for t in ts:
            # if is_indicator(t):
            #     diff = indicator_level(indicator)-indicator_level(t) + 1
            #     indi = move_indicator(t, max(0, diff))
            #     tactics.appendleft(indi)
            # else:
            tactics.appendleft(t)
        # tactics.appendleft(indicator)
            
    
    def qed(self):
        state_ids, response, exn = self.serapi.try_add_and_execute('Qed.')
        return state_ids[0] > 0 and not exn


    def log(self):
        history_log = self.history.log()
        llm_log = self.llm.log()
        return {'history': history_log, 'chat': llm_log, 'original': self.original, 'hammer_times': self.hammer_times}
    

if __name__ == '__main__':
    tactics = '''```   \nintros st h d l l' n H_sane H_seen H_eq H_process.\ndestruct st as [packets state].\nsimpl in H_process. inversion H_process. subst.\nunfold revertNetwork. simpl. f_equal.\n- unfold update. extensionality y.\n  destruct (name_eq_dec h y); auto.\n- extensionality y. destruct (name_eq_dec h y); auto.\nQed'''
    with SerAPI(60) as serapi:
        parsed, exn = tactic_unifier(serapi, tactics)
        print(exn)
        for p in parsed:
            print(p)
