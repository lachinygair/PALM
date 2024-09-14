from .config import *
from .utils import *
import os
from pathlib import Path

intersection_file = 'intersection.json'


def success_total(exp_names, projs, merge=False):
    res = {}
    all = {}
    for exp in exp_names:
        for proj in projs:
            if type(proj) is tuple and len(proj) == 2:
                proj, proj_res = proj
            else:
                proj_res = proj
            path = os.path.join(proof_path, exp, proj)
            files = set([f for f in files_in_rec(path) if f.endswith('json')])
            for file in files:
                data = json.load(open(os.path.join(path, file)))
                data = data[-1]
                record = {r: data['history'][r] for r in ['proof', 'repairs', 'exceptions', 'time'] if r in data['history']}
                if data['succ']:
                    res[os.path.join('' if merge else exp, proj_res, file)] = record
                all[os.path.join('' if merge else exp, proj_res, file)] = record
    return res, all


def sucess_difference(exps1, exps2, projs, reverse=False):
    inter_ = json.load(open(os.path.join(data_path, intersection_file)))
    inter = set()
    for p in projs:
        inter.update({r + '.json' for r in inter_[p]})
    if reverse:
        exps1, exps2 = exps2, exps1
    # all, _ = success_total(exps1+exps2, projs)
    # all = set(all.keys()).intersection(inter)
    res_exp1, _ = success_total(exps1, projs)
    res_exp2, _ = success_total(exps2, projs)
    res_exp1 = set(res_exp1.keys())
    res_exp2 = set(res_exp2.keys())
    res_exp1 = [r[r.find('/')+1:] for r in res_exp1]
    res_exp2 = [r[r.find('/')+1:] for r in res_exp2]
    res_exp1 = [r for r in res_exp1 if r in inter]
    res_exp2 = [r for r in res_exp2 if r in inter]
    res_exp1 = set(res_exp1)
    res_exp2 = set(res_exp2)
    # for theorem in all.keys():
    #     parts = Path(theorem).parts
    #     exp, name = parts[0], os.path.join(*(parts)[1:])
    #     if name in inter:
    #         if exp in exps1:
    #             res_exp1.add(name)
    #         if exp in exps2:
    #             res_exp2.add(name)
    
    res = res_exp1.difference(res_exp2)
    for r in res:
        print('test/'+r)
        # print(os.path.join(proof_path, exps1[0], r), '\n', os.path.join(proof_path, exps2[0], r), '\n', os.path.join(proof_path, 'origin', r))
    # print('rm ' + ' '.join(['\"'+os.path.join(proof_path, 'ours_new_gpt', r)+'\"' for r in res]))
    print(len(res))
    return res, None


def evaluate_approach_total(result1, result2):
    res1, all1 = result1
    res1 = set(res1.keys()) if type(res1) is dict else res1
    all1 = set(all1.keys()) if type(all1) is dict else all1
    res2, all2 = result2
    res2 = set(res2.keys()) if type(res2) is dict else res2
    all2 = set(all2.keys()) if type(all2) is dict else all2
    all = all1 & all2
    res = all & (res1 | res2) | res1
    return res, all


def evaluate_success_time(res):
    total = 0
    for r in res.values():
        total += r['time']
    print(total/len(res))


def see_diff(proj, exp: str):
    res, all = success_total([exp], [proj], merge=True)
    # for r in res:
    #     print(r)
    all = {k for k in all.keys()}
    all_total = {p+'.json' for p in ours([proj])[0]}
    diff = all_total.difference(all)
    print(proj, len(res), len(all), len(diff))
    # for d in diff:
    #     print(d)


def see_all_ours(exps, projs, show_diff=False):
    # back_all_skip_fail origin
    res_succ = set()
    res_all = set()
    print('succ | total | diff')
    total_succ, total_all, total_diff = 0, 0, 0
    inter = json.load(open(os.path.join(data_path, intersection_file)))
    inter = {p: {r + '.json' for r in inter[p]} for p in projs if p in inter}
    for p in projs:
        if p not in inter:
            continue
        succ, all = success_total(exps, [p], merge=True)
        succ, all = set(succ.keys()), set(all.keys())
        succ.intersection_update(inter[p])
        all.intersection_update(inter[p])
        diff = inter[p].difference(all)
        total_succ += len(succ)
        total_all += len(all)
        total_diff += len(diff)
        print(p, '|', len(succ), '|', len(all), '|', len(diff))
        res_succ.update(succ)
        res_all.update(all)
        if show_diff:
            for d in diff:
                print(d)
    return res_succ, res_all


if __name__ == '__main__':
    proj_all = 'weak-up-to buchberger jordan-curve-theorem dblib disel zchinese zfc dep-map chinese UnifySL hoare-tut huffman PolTac angles coq-procrastination coq-library-undecidability tree-automata coquelicot fermat4 demos coqoban goedel verdi-raft verdi zorns-lemma coqrel fundamental-arithmetics'
    proj_v11 = "weak-up-to buchberger dblib disel zchinese zfc dep-map chinese hoare-tut huffman PolTac \
      angles coq-procrastination fermat4 demos coqoban goedel verdi-raft zorns-lemma fundamental-arithmetics".split()
    projs = proj_all.split()
    projs = [p for p in projs if p != 'verdi']
    # projs = ['weak-up-to']

# back_all_skip_fail ours back_no_bullet back_no_intros origin best_hammer , 'ours_new_llama', 'ours_new', 'best_hammer'
    # res_succ, res_all = see_all_ours(['test', 'hammer'], projs, False)
    # print(len(res_succ), len(res_all))
    sucess_difference(['ours'], ['test', 'hammer'], ['disel'], False)

    # res_succ, res_all = see_all_ours(['ours_new'], projs, False)
    # res_succ_hammer, _ = see_all_ours(['best_hammer'], projs, False)
    # res = set()
