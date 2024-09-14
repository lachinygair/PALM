import re
from .serapi import CoqExn, SerAPI
from .retrieval import bm25, process_id
from collections import deque
from .utils import *


ERR_MSG = r'\(str "(.*?)"\)'
UNFINISHED_BULLET = r'Wrong bullet (.*?): Current bullet (.*?) is not finished'
WRONG_BULLET = r'Wrong bullet (.*?): Expecting (.*?)\.'
WRONG_BULLET_UNFOUCS = r'Wrong bullet (.*?): Try unfocusing with "(.*?)"\.'
NO_MORE_GOALS = r'Wrong bullet (.*?): No more goals' # todo
NO_MORE_SUBGOALS = r'Wrong bullet (.*?): No more subgoals'
FAILED_BULLET = r'Proof_bullet.Strict.FailedBullet'
WRONG_UNFOCUS = r'This proof is focused, but cannot be unfocused this way' # }. todo
NEXT_GOAL = r'No such goal. Focus next goal with bullet (.*?)\.'
NO_GOAL = r'No such goal'
USED_VAR = r'(.*?) is ((already used)|(used twice))'

RE_QUERY = 'Error with {tactic}: {msg}. Give a new proof starting from it.'


# def log(t, ts):
#     out_file = os.path.join(proof_path, exp_name, file_name, theorem_name+'.json')        
#     create_dir(out_file)
#     if os.path.exists(out_file):
#         with open(out_file) as f:
#             result = json.load(f)
#         with open(out_file, 'w') as f:
#             result_new = state.log()
#             result_new['succ'] = succ
#             result.append(result_new)
#             json.dump(result, f)
#     else:
#         with open(out_file, 'w') as f:
#             result = state.log()
#             result['succ'] = succ
#             json.dump([result], f)

def unfinished_bullet(msg, groups, state, tactics: deque):
    if len(state.fg_goals) == 1:
        return ['shelve.']
    else:
        bullet = state.next_indicator()
        return ['shelve.', bullet] * len(state.fg_goals)


def wrong_bullet(msg, groups, state, tactics: deque):
    _, bullet = groups
    tactics.popleft()
    # tactics.appendleft(bullet)
    return [bullet]


def wrong_bullet_unfocus(msg, groups, state, tactics: deque):
    _, unfocus = groups
    tactics.popleft()
    # tactics.appendleft(unfocus)
    return [unfocus]


def no_more_goals(msg, groups, state, tactics: deque):
    while tactics:
        tactics.pop()


def no_more_subgoals(msg, groups, state, tactics: deque):
    while tactics:
        tactics.pop()


def failed_bullet(msg, groups, state, tactics: deque):
    # tactics.appendleft('shelve.')
    return ['shelve.']


def wrong_unfocus(msg, groups, state, tactics: deque):
    # tactics.appendleft('shelve.')
    return ['shelve.']

def next_goal(msg, groups, state, tactics: deque):
    bullet = groups[0]
    assert type(tactics[0]) is tuple and type(tactics[0][1]) is str
    while tactics and not tactics[0][0] == bullet:
        tactics.popleft()


def no_goal(msg, groups, state, tactics: deque):
    while tactics:
        tactics.pop()


def used_var(msg, groups, state, tactics: deque):
    def check_char(c):
        return not (c.isalnum() or c in {"_", "'"})
    def replace_qualid(tactic: str, pattern: str, rep: str):
        ind = -1
        while ind < len(tactic):
            ind = tactic.find(pattern, ind+1)
            if ind-1>=0 and check_char(tactic[ind-1]) \
                and ind + len(pattern) < len(tactic) and check_char(tactic[ind + len(pattern)]):
                res = tactic[:ind] + rep + tactic[ind + len(pattern):]
                return res

    assert type(tactics[0]) is tuple and type(tactics[0][1]) is str
    used = groups[0]
    tactic, _ = tactics.popleft()
    new_name = used + "'"
    while new_name in tactic:
        new_name += "'"
    new_tac = replace_qualid(tactic, used, new_name)
    return [new_tac]

    # tactic = normalize_spaces(tactic)
    # hypos = state.fg_goals[0]['hypos']
    # tactic_sp = [t.strip() for t in tactic.split(';')]
    # new_tactic_sp = []

    # for tactic in tactic_sp:
    #     if tactic.startswith('intros'):
    #         intros = extract_qualids(tactic)
    #         intros_new = [intro for intro in intros if intro not in hypos and intro != used]
    #         new_tactic = tactic.replace(' '.join(intros), ' '.join(intros_new))
    #         new_tactic_sp.append(new_tactic)
    #     elif ' as ' in tactic:
    #         tactic = tactic[:tactic.find(' as ')]
    #         new_tactic_sp.append(tactic)
    # new_tactic = '; '.join(new_tactic_sp)
    # if not new_tactic.endswith('.'):
    #     new_tactic += '.'
    # return [new_tactic]


WRONG_TYPE = r'The term (.*?) has type (.*?) while it is expected to have type (.*?)\.'
CANNOT_UNIFY = r'Unable to unify (.*?) with (.*?)\.'
VAR_NOT_FOUND = r'The variable (.*?) was not found in the current environment'
REF_NOT_FOUND = r'The reference (.*?) was not found in the current environment'
NO_SUBTERM = r'Found no subterm matching (.*?) in (.*?)\.' # rewrite. todo
NO_HYPOS = r'No such hypothesis: (.*?)' # rewrite xx in yy, no yy. todo
CANNOT_SUBST = r'Cannot find any non-recursive equality over (.*?)\.' # subst xx. todo.
NUM_BRANCH = r'Expects a (disjunctive|conjunctive) pattern with (.*?) branches'  # todo
NUM_BRANCH_BOTH = r'Expects a disjunctive pattern with (.*?) branch or a conjunctive pattern made of (.*?) patterns'
CANNOT_INFER_PARA = r'Cannot infer the implicit parameter (.*?) of (.*?) whose type is (.*?)\.' # todo
CANNOT_TURN_IND = r'Cannot turn inductive (.*?) into an evaluable reference' # todo
CANNOT_APPLY_IN = r'Unable to apply lemma of type (.*?) on hypothesis of type (.*?)\.' # todo
NOT_REFLEXIVE = r'The relation (.*?) is not a declared reflexive relation' # todo
EXP_CANNOT_APPLY = r'The expression (.*?) of type (.*?) cannot be applied to the term (.*?) : (.*?)\.'
TERM_CANNOT_APPLY = r'The term (.*?) of type (.*?) cannot be applied to the terms (.*?) The (.*?) term has type (.*?) which should be coercible to (.*?)\.'
NO_INSTANCE_VAR = r'Unable to find an instance for the variables? (.*?)\.'
NO_SUCH_BOUND = r'No such bound variable (.*?)\.' # todo eg. rewrite H with (a:=b), no such bound a


def wrong_type(msg, groups, state, tactics: deque):
    term, type, type_expected = groups
    tactics.popleft()


def cannot_unify(msg, groups, state, tactics: deque):
    assert type(tactics[0]) is tuple and type(tactics[0][1]) is str
    tactic, _ = tactics.popleft()
    if tactic == 'reflexivity.':
        return ['auto.']
    else:
        qualids = extract_qualids(tactic)
        hypos = set(state.fg_goals[0]['hypos'].keys() if state.fg_goals != [] else [])
        for q in qualids:
            if q not in hypos and state.serapi.check(q) is not None:
                pr = process_id(q, state.serapi, False)
                if pr and pr[0] != 'Ltac':
                    state.use_qualids.add(q)
        return ['qsimpl time: 1 use: %s.' % ','.join(state.use_qualids)] if state.use_qualids else ['qsimpl time: 1.']
    

def var_not_found(msg, groups, state, tactics: deque):
    tactics.popleft()


def ref_not_found(msg, groups, state, tactics: deque):
    assert type(tactics[0]) is tuple and type(tactics[0][1]) is str
    unknown_ref = groups[0]
    tactic_err, _ = tactics.popleft()
    if tactic_err.startswith('qsimpl'):
        qualids = extract_qualids(tactic_err)
        qualids = [q for q in qualids if q not in ['qsimpl', 'time', 'use'] and ':' not in q and q != unknown_ref]
        return ['qsimpl time: 1 use: %s.' % ','.join(qualids)] if qualids else ['qsimpl time: 1.']
    candidates = state.serapi.predict(300)
    if candidates == []:
        return
    candidates = [process_id(id, state.serapi) for id in candidates]
    candidates = [state.serapi.query_qualid(p[1]) for p in candidates if (p and p[0] != 'Ltac')]
    candidates = set(candidates)
    if state.fg_goals != []:
        hypos = state.fg_goals[0]['hypos'].keys()
        candidates.update(hypos)
    candidates = list(candidates)
    query_bm25 = bm25(candidates, sp='_')
    res = query_bm25(unknown_ref)
    for ref in res[:100]:
        tactic = tactic_err.replace(unknown_ref, ref)
        state_ids, responses, err = state.serapi.try_add_and_execute(tactic, timeout=5)
        if state_ids != [-1] and err == None:
            state.serapi.cancel(state_ids)
            # tactics.appendleft(tactic)
            return [tactic]
    return []


def no_subterm(msg, groups, state, tactics: deque):
    assert type(tactics[0]) is tuple and type(tactics[0][1]) is str
    rewrite, _ = tactics.popleft()
    pattern = r"(rewrite\s*(<-|->)?\s*)(.+?)(?:\s+in\s+[a-zA-Z_][a-zA-Z0-9_'']*)?\.$"
    match = re.search(pattern, rewrite)
    if match:
        direction = match.group(2) or ''
        term = match.group(3).strip()
        if state.serapi.check(term) is not None:
            new_tactic = f"try rewrite {direction} {term} in *; auto."
            if state.serapi.query_qualid(term) is not None:
                state.use_qualids.add(term)
            # tactics.appendleft(new_tactic)
            return [new_tactic]
 

def no_hypos(msg, groups, state, tactics: deque):
    tactics.popleft()


def cannot_subst(msg, groups, state, tactics: deque):
    tactics.popleft()


def num_branch(msg, groups, state, tactics: deque):
    tactics.popleft()


def num_branch_both(msg, groups, state, tactics: deque):
    tactics.popleft()


def cannot_infer_para(msg, groups, state, tactics: deque):
    tactics.popleft()


def cannot_turn_ind(msg, groups, state, tactics: deque):
    tactics.popleft()


def cannot_apply_in(msg, groups, state, tactics: deque):
    tactics.popleft()


def not_reflexive(msg, groups, state, tactics: deque):
    tactics.popleft()
    # tactics.appendleft('qsimpl')
    return ['qsimpl']


def exp_cannot_apply(msg, groups, state, tactics: deque):
    tactics.popleft()


def term_cannot_apply(msg, groups, state, tactics: deque):
    tactics.popleft()


def no_instance_var(msg, groups, state, tactics: deque):
    tactics.popleft()


def no_such_bound(msg, groups, state, tactics: deque):
    tactics.popleft()


TACTIC_FAILURE = r'Tactic failure: (.*?) failed'
NO_CONTRADICTION = r'No such contradiction'
CONGRU_FAILED = r'congruence failed'
NO_REWRITE_RELATION = r'Cannot find a relation to rewrite'
NO_REWRITE_HOMO = r'Cannot find an homogeneous relation to rewrite'
NO_MATCH_TERM = r'The LHS of (.*?) does not match any subterm of the goal' # todo. rewrite (forall xxx...)
NO_EQUALITY = r'No primitive equality found' # discriminate/injection. todo.
NOTHING_INJECT = r'Nothing to inject' # todo
NO_PRODUCT = r'No product even after head-reduction' # intros. todo
NOT_EVALUABLE = r'Cannot coerce (.*?) to an evaluable reference' # cannot be used with a tactic. todo
NOT_INDUCTIVE_PRODUCT = r'Not an inductive product' # todo
NOT_INDUCTIVE_GOAL = r'Not an inductive goal with (.*?) constructor' # todo
NO_ENOUGH_PREMISES = r'Applied theorem does not have enough premises' # todo


def tactic_failure(msg, groups, state, tactics: deque):
    tactics.popleft()
    # tactics.appendleft('qsimpl')
    return ['qsimpl']


def no_contradiction(msg, groups, state, tactics: deque):
    tactics.popleft()
    # tactics.appendleft('qsimpl')
    return ['qsimpl']


def congru_failed(msg, groups, state, tactics: deque):
    tactics.popleft()
    # tactics.appendleft('qsimpl')
    return ['qsimpl']


# rewrite xx, but xx is not an equation
def no_rewrite_relation(msg, groups, state, tactics: deque):
    tactics.popleft()


def no_rewrite_homo(msg, groups, state, tactics: deque):
    tactics.popleft()


def no_match_term(msg, groups, state, tactics: deque):
    tactics.popleft()


def no_equality(msg, groups, state, tactics: deque):
    tactics.popleft()


def nothing_inject(msg, groups, state, tactics: deque):
    tactics.popleft()


def no_product(msg, groups, state, tactics: deque):
    tactics.popleft()
    return ['intros.']


def not_evaluable(msg, groups, state, tactics: deque):
    tactics.popleft()
    # tactics.appendleft('qsimpl')
    return ['qsimpl']


def not_inductive_product(msg, groups, state, tactics: deque):
    tactics.popleft()
    # tactics.appendleft('qsimpl')
    return ['qsimpl']


def not_inductive_goal(msg, groups, state, tactics: deque):
    tactics.popleft()
    # tactics.appendleft('qsimpl')
    return ['qsimpl']


def no_enough_premises(msg, groups, state, tactics: deque):
    tactics.popleft()


# all_errs = {
#     'unfinished_bullet': (UNFINISHED_BULLET, unfinished_bullet),
#     'wrong_bullet': (WRONG_BULLET, wrong_bullet),
#     'no_more_goals': (NO_MORE_GOALS, no_more_goals),
#     'no_more_subgoals': (NO_MORE_SUBGOALS, no_more_subgoals),
#     'failed_bullet': (FAILED_BULLET, failed_bullet),
#     'next_goal': (NEXT_GOAL, next_goal),
#     'no_goal': (NO_GOAL, no_goal),
#     # 'wrong_unfocus': (WRONG_UNFOCUS, wrong_unfocus), # 3

#     # 'used_var': (USED_VAR, used_var),
#     # 'no_product': (NO_PRODUCT, no_product), # 2

#     'ref_not_found': (REF_NOT_FOUND, ref_not_found), 

#     'no_hypos': (NO_HYPOS, cannot_unify), # 1
#     'cannot_unify': (CANNOT_UNIFY, cannot_unify),
#     'cannot_apply_in': (CANNOT_APPLY_IN, cannot_unify),
#     'exp_cannot_apply': (EXP_CANNOT_APPLY, cannot_unify), 
#     'no_instance_var': (NO_INSTANCE_VAR, cannot_unify), 
#     'wrong_type': (WRONG_TYPE, cannot_unify), 
#     'var_not_found': (VAR_NOT_FOUND, cannot_unify),
#     'cannot_infer_para': (CANNOT_INFER_PARA, cannot_unify), # 4
#     'no_match_term': (NO_MATCH_TERM, cannot_unify),
#     'no_subterm': (NO_SUBTERM, cannot_unify), 
#     'no_rewrite_relation': (NO_REWRITE_RELATION, cannot_unify), # 5
#     'not_inductive_product': (NOT_INDUCTIVE_PRODUCT, cannot_unify),
#     'not_inductive_goal': (NOT_INDUCTIVE_GOAL, cannot_unify),
#     'not_evaluable': (NOT_EVALUABLE, cannot_unify),
#     'cannot_turn_ind': (CANNOT_TURN_IND, cannot_unify), # 6
#     # 'tactic_failure': (TACTIC_FAILURE, tactic_failure),
#     # 'no_contradiction': (NO_CONTRADICTION, no_contradiction),
#     # 'congru_failed': (CONGRU_FAILED, congru_failed),
#     # 'cannot_subst': (CANNOT_SUBST, cannot_subst),
#     # 'no_equality': (NO_EQUALITY, no_equality),
#     # 'nothing_inject': (NOTHING_INJECT, nothing_inject),
#     # 'not_reflexive': (NOT_REFLEXIVE, not_reflexive), # 7
# }

errors_bullet = {
    'unfinished_bullet': (UNFINISHED_BULLET, unfinished_bullet),
    'wrong_bullet': (WRONG_BULLET, wrong_bullet),
    'no_more_goals': (NO_MORE_GOALS, no_more_goals),
    'no_more_subgoals': (NO_MORE_SUBGOALS, no_more_subgoals),
    'failed_bullet': (FAILED_BULLET, failed_bullet),
    'next_goal': (NEXT_GOAL, next_goal),
    'no_goal': (NO_GOAL, no_goal),
    # 'wrong_unfocus': (WRONG_UNFOCUS, wrong_unfocus), # 3
}

errors_intros = {
    'used_var': (USED_VAR, used_var),
    'no_product': (NO_PRODUCT, no_product), # 2
}

errors_ref = {
    'ref_not_found': (REF_NOT_FOUND, ref_not_found), 
    'var_not_found': (VAR_NOT_FOUND, ref_not_found),
}

errors_type = {
    'no_hypos': (NO_HYPOS, cannot_unify), # 1
    'cannot_unify': (CANNOT_UNIFY, cannot_unify),
    'cannot_apply_in': (CANNOT_APPLY_IN, cannot_unify),
    'exp_cannot_apply': (EXP_CANNOT_APPLY, cannot_unify), 
    'no_instance_var': (NO_INSTANCE_VAR, cannot_unify), 
    'wrong_type': (WRONG_TYPE, cannot_unify), 
    'cannot_infer_para': (CANNOT_INFER_PARA, cannot_unify), # 4
    'no_match_term': (NO_MATCH_TERM, cannot_unify),
    'no_subterm': (NO_SUBTERM, cannot_unify), 
    'no_rewrite_relation': (NO_REWRITE_RELATION, cannot_unify), # 5
    'not_inductive_product': (NOT_INDUCTIVE_PRODUCT, cannot_unify),
    'not_inductive_goal': (NOT_INDUCTIVE_GOAL, cannot_unify),
    'not_evaluable': (NOT_EVALUABLE, cannot_unify),
    'cannot_turn_ind': (CANNOT_TURN_IND, cannot_unify), # 6
}

unhandle_errors = {
    'num_branch': (NUM_BRANCH, num_branch),
    'num_branch_both': (NUM_BRANCH_BOTH, num_branch_both), # 8
    'term_cannot_apply': (TERM_CANNOT_APPLY, term_cannot_apply),
    'no_such_bound': (NO_SUCH_BOUND, no_such_bound),
    'no_rewrite_homo': (NO_REWRITE_HOMO, no_rewrite_homo),
    'no_enough_premises': (NO_ENOUGH_PREMISES, no_enough_premises),
}


class Repair:
    def __init__(self) -> None:
        self.handle_errors = {}
        all_errors = {
            'bullet': errors_bullet,
            'intros': errors_intros,
            'ref': errors_ref,
            'type': errors_type
        }
        for k, v in all_errors.items():
            self.handle_errors.update(v)
    

    def repair(self, msg: str, state, tactics: deque):
        msg = msg.replace('\\n', '\n').replace('\n', ' ').replace('\\"', '\"')
        msg = normalize_spaces(msg)
        tactic, _ = tactics[0]
        for name, (pattern, handler) in self.handle_errors.items():
            match = re.search(pattern, msg)
            if match is not None:
                groups = match.groups()
                extend = handler(msg, groups, state, tactics)
                if extend is not None:
                    tactics.extendleft([(t, name) for t in extend])
                state.history.add_exn(tactic, msg, name, True)
                return True
                    
        for name, (pattern, handler)in unhandle_errors.items():
            match = re.search(pattern, msg)
            if match is not None:
                state.history.add_exn(tactics[0], msg, name)
        return False
    

# def replace_coq_tactic(input_string, pattern, replace):
#         regex_pattern = r"[^\w']"+ re.escape(pattern) + r"[^\w']"
#         replaced_string = re.sub(regex_pattern, replace, input_string)
#         return replaced_string


err_var = '(str "Unable to find an instance for the variables x, y.")'
num_bran = 'Expects a disjunctive pattern with 32 branches.'
err_unify = '(str "Unable to unify "ev (S (S ?M1401))\" with\n \"@ex nat (fun n : nat => @eq nat 0 (double n))".")'
err_unify2 = '(str "In environment\\nn\' : nat\\nH\' : ev n\'\\nIH : Even n\'\\nUnable to unify \\"ev (S (S ?M1401))\\" with\\n \\"@ex nat (fun n : nat => @eq nat (S (S n\')) (double n))\\".")'
test = '(Proof\.CannotUnfocusThisWay)'

if __name__ == '__main__':
    pass
