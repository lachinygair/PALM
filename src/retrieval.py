from rank_bm25 import BM25Okapi
from .utils import *
from .serapi import *


def split_into_chunks(text, chunk_size=500):
    tokens = text.split()
    for i in range(0, len(tokens), chunk_size):
        yield ' '.join(tokens[i:i + chunk_size])


def bm25(contexts, sp=' '):
    corpus = [s.split(sp) for s in contexts]
    bm25 = BM25Okapi(corpus)
    def query(q: str, top=300):
        q = q.split(sp)
        scores = bm25.get_scores(q)
        top_indices = np.argsort(scores)[::-1][:top]
        top_contexts = [contexts[i] for i in top_indices]
        return top_contexts
    return query


def extract_defs(goal_hypo_types, env_types):
    res = {}
    rm = set()
    for tp in goal_hypo_types:
        qds = set(extract_qualids(tp))
        for q in qds:
            if q in env_types:
                res[q] = env_types[q]
            else:
                rm.add(q)
    
    diff_ = set(res.keys())
    while diff_:
        diff = diff_.copy()
        diff_.clear()
        for qualid in diff:
            qds = set(extract_qualids(env_types[qualid]))
            qds.difference_update(rm)
            qds.difference_update(diff)
            qds.difference_update(res.keys())
            for q in qds:
                if q in env_types:
                    res[q] = env_types[q]
                    diff_.add(q)
                else:
                    rm.add(q)
    return res


def extract_const_induct(constants, inductives):
    consts = [(c['sort'], c['short_ident'], c['type']) for c in constants] # if not c['qualid'].startswith('Coq.')
    inds = []
    for inductive in inductives:
        if len(inductive['blocks']) == 1:
            block = inductive['blocks'][0]
            # if not in_std(block['qualid']):
            tmp = block['constructors']
            block['constructors'] = []
            for constructor in tmp:
                block['constructors'].append([c for c in constructor if c])
            inds.append((block['short_ident'], ' | '.join([' : '.join(c) for c in block['constructors']])))
    env_types = {c[1]: c[2] for c in consts}
    for i in inds:
        env_types[i[0]] = i[1]
    env_types = {k.split('.')[-1]: v for k, v in env_types.items()}
    return consts, inds, env_types


def process_id(id: str, serapi: SerAPI, skip_std=True):
    if id.startswith('SerTop.'):
        id = id[len('SerTop.'):]
    locate = serapi.locate(id)
    # check = serapi.check(id)
    if locate is None:
        return None
    try:
        tp, lc = locate.split()
        if lc.startswith('SerTop.'):
            lc = lc[len('SerTop.'):]
        if skip_std and lc.startswith('Coq.Init.'):
            return None
        return (tp, lc)
    except Exception:
        return None


class Retrieval:    
    premises_cache = {}
    searches_cache = set()
    check_timeout = 0

    def __init__(self) -> None:
        self.non_premises_cache = set()
        self.premises_covered = set()


    def add_contexts(self, serapi: SerAPI, starts, avoids):
        ids_all = set()
        constr = ' '.join(starts)
        constr = constr.replace('\n', ' ').strip()
        ids = extract_qualids(constr)
        ids = [id for id in ids if not (id in avoids or id in self.non_premises_cache)]
        for id in ids:
            if id in Retrieval.premises_cache:
                ids_all.add(id)
                continue
            elif id in self.non_premises_cache:
                continue
            try:
                premise = self.process_id(serapi, id, avoids)
                if premise != None:
                    ids_all.add(id)
            except CoqExn as e:
                print('get_premises '+str(e))
                self.non_premises_cache.add(id)
        return ids_all
    

    def generate_query(self, goals):
        goal_hypo_types = set([g['goal'] for g in goals])
        for g in goals:
            goal_hypo_types.update(g['hypos'].values())
        return '-> '.join(goal_hypo_types)


    def check_print(self, serapi: SerAPI, tp, ident):
        check = None
        if self.check_timeout < 5:
            check = serapi.check(ident)
            if not check:
                self.check_timeout += 1
        if check and ('forall' in check or 'exists' in check or '∀' in check ):
            return check
        prt = serapi.print(ident)
        if prt != None:
            return prt
        else:
            return check
    

    def retrieve_predict(self, serapi: SerAPI, goals, tech='bm25', top=50):
        qualids = set()
        defs = set()
        defs_idents = set()
        hypos = set()
        for goal in goals:
            hypos.update(goal['hypos'].keys())
            for exp in [goal['goal']] + list(goal['hypos'].values()):
                qualids.update(extract_qualids(exp))
        qualids.difference_update(hypos)
        for qualid in qualids:
            pr = process_id(qualid, serapi, False)
            short_ident = serapi.query_qualid(qualid)
            if pr is not None:
                content = self.check_print(serapi, pr[0], pr[1])
                defs_idents.add(short_ident)
                defs.add(content)
            
        p300 = serapi.predict(300)
        p300 = [process_id(id, serapi, False) for id in p300]
        p300 = [p for p in p300 if p]
        context = set()
        lemmas = []
        for tp, ident in p300:
            short_ident = serapi.query_qualid(ident)
            if tp == 'Variable' or short_ident in defs_idents:
                continue
            if tp == 'Inductive':
                if short_ident not in defs_idents:
                    content = serapi.print(ident)
                    context.add(content)
            else:
                content = self.check_print(serapi, tp, ident)
                context.add(content)
                if tp == 'Constant':
                    lemmas.append(short_ident)
        query = self.generate_query(goals)
        if tech == 'bm25':
            query_bm25 = bm25(list(context))
            res = query_bm25(query)
        return res[:top], list(defs), lemmas #, list(defs_idents)

    
    def retrieve_env_all(self, goals, env, tech='bm25', top=50):
        query = self.generate_query(goals)

        constants, inductives = env['constants'], env['inductives']
        consts, inds, env_types = extract_const_induct(constants, inductives)
        context = ['%s %s := %s'%c for c in consts]
        context += ['Inductive %s := %s'%i for i in inds]
        if tech == 'bm25':
            query_bm25 = bm25(list(context))
            res = query_bm25(query)
        return res[:top]
    

if __name__ == '__main__':
    pass
