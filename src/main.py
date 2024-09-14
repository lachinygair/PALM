from .serapi import *
from .utils import *
from .llm import LLM
from .framework import State
from .repair import Repair
from .retrieval import Retrieval
import json
import traceback
import multiprocessing
import argparse
from pathlib import Path


def log(state: State, exp_name: str, file_name: str, theorem: str, succ: bool):
    out_file = os.path.join(proof_path, exp_name, file_name, theorem+'.json')        
    create_dir(out_file)
    if os.path.exists(out_file):
        with open(out_file) as f:
            result = json.load(f)
        with open(out_file, 'w') as f:
            result_new = state.log()
            result_new['succ'] = succ
            result.append(result_new)
            json.dump(result, f)
    else:
        with open(out_file, 'w') as f:
            result = state.log()
            result['succ'] = succ
            json.dump([result], f)
        

def prove(state: State, file_name: str, proof_data, resume='', backtrack=False):
    tactics = ''
    proof_name = proof_data['name']
    if resume != '':
        json_file = os.path.join(proof_path, resume, file_name, proof_name+'.json')
        if os.path.exists(json_file):
            with open(json_file) as f:
                data = json.load(f)
                tactics = data[-1]['original']
                if tactics == '':
                    tactics = 'intros.'
                    # raise Exception('resume failed: original proof is empty')
    
    print('original resume: ', tactics) 
    
    succ = state.prove(tactics_ori=tactics)
    if not succ and backtrack:
        succ = state.backtrack()
    if succ:
        return state.qed()
    else:
        return False


def prove_hammer_only(state: State):
    succ = state.prove_with_hammer()
    if succ:
        return state.qed()
    else:
        return False

    
def prove_file(file: str, exp_name='test', theorem='', resume='', backtrack=False, skip=False, intersect=False):
    print(file)
    proj = Path(file).parts[0]
    intersection = json.load(open((os.path.join(data_path, 'intersection.json'))))[proj]
    code, path_option, version, theorems = prepare(file)
    if theorems == []:
        return
    with SerAPI(300, version, debug=False, options=path_option) as serapi:
        cur_ind = 0
        i = 0
        if theorem != '':
            while i < len(theorems) and theorems[i]['name'] != theorem:
                i += 1
            if i >= len(theorems):
                return
            theorems = [theorems[i]]
        for index, proof in enumerate(theorems):
            if intersect and os.path.join(file, proof['name']) not in intersection:
                continue
            # if proof['name'] in ['this_not_pts', 'validV', 'this_not_pts', 'sval_mono', 'hook_complete_unit']:
            #     continue
            path = os.path.join(proof_path, exp_name, file, proof['name']+'.json')
            path_resume = os.path.join(proof_path, resume, file, proof['name']+'.json')
            if skip and os.path.exists(path):
                continue

            for i, c in enumerate(code[cur_ind: proof['begin']+1]):
                state_ids, _ = serapi.add_and_execute(c)
            print('start prove: ', proof['name'])
            llm = LLM()
            repair = Repair()
            state = State(serapi=serapi, llm=llm, repair=repair)
            state.file = os.path.join(file, proof['name']+'.json')
            state.retrieval = Retrieval()
            succ = False
            try:
                serapi.add_and_execute('From Hammer Require Import Hammer Tactics.')
                serapi.add_and_execute('Proof. Set Bullet Behavior "Strict Subproofs".')
                serapi.add_and_execute('Set Hammer ATPLimit 10.')

                succ = prove(state, file, proof, resume, backtrack=backtrack)
                log(state, exp_name, file, proof['name'], succ)
                serapi.cancel(state_ids)
            except Exception as e:
                print('prover err:', print(proof['name']), str(e))
                stack_trace = traceback.format_exc()
                log_file = os.path.join(proof_path, exp_name, 'log.txt')
                create_dir(log_file)
                with open(log_file, 'a') as f:
                    f.write(file + ' ' + proof['name'] + '\n' + stack_trace + '\n')
                serapi.cancel(state_ids)
                return proof['name']

            cur_ind = proof['begin']
    return None


def run(proj, threads=1, exp_name='', theorem='', resume='', backtrack=False, skip=False, intersect=False):
    files = [f for f in files_in_rec(os.path.join(data_path, proj)) if f.endswith('.json')]
    if threads > 1:
        args = [(os.path.join(proj, f), exp_name, theorem, resume, backtrack, skip, intersect) for f in files]
        pool = multiprocessing.Pool(processes=threads)
        pool.starmap(prove_file, args)
        pool.close()
        pool.join()
    else:
        for f in files:
            prove_file(file=os.path.join(proj, f), exp_name=exp_name, theorem=theorem, \
                        resume=resume, backtrack=backtrack, skip=skip, intersect=intersect)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--proj', type=str)
    parser.add_argument('--exp_name', default='test', type=str)
    parser.add_argument('--threads', default=1, type=int)
    parser.add_argument('--theorem', default='', type=str)
    parser.add_argument('--resume', default='', type=str)
    parser.add_argument('-skip', default=False, action='store_true')
    parser.add_argument('-backtrack', default=False, action='store_true')
    parser.add_argument('-intersect', default=False, action='store_true')

    args = parser.parse_args()

    run(proj=args.proj, threads=args.threads, exp_name=args.exp_name, theorem=args.theorem, resume=args.resume, \
        backtrack=args.backtrack, skip=args.skip, intersect=args.intersect)
 