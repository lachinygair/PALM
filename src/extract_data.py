from .utils import *
from .config import *
from .serapi import *
import os
import json
import multiprocessing
import argparse


def get_code(coq_code):
    def loc2code(bp, ep):
        code = coq_code[bp:ep]
        try:
            code = code.strip().decode("utf-8")
        except UnicodeDecodeError:
            code = code.decode(chardet.detect(code)["encoding"]).strip()
        code = normalize_spaces(remove_comments(code))
        return code
    return loc2code


def extract_file(proj: str, file: str):
    print('extracting:', file)
    path_option = ''
    if proj:
        options, version = json.load(open(os.path.join(data_path, 'path.json')))[proj]
        options = [op.strip() for op in options.split()]
        path_option = ''
        for i, option in enumerate(options):
            if i % 3 == 1:
                path_option += os.path.join(projects_path, proj, option) + ','
            else:
                path_option += option + ' '
    source = open(file, "rb").read()
    source = source.strip().decode("utf-8")
    source = normalize_spaces(source)
    src_len = len(source)
    with SerAPI(600, debug=False, options=path_option, version=version) as serapi:
        codes, exn = serapi.parse(source)
        codes_len = sum([len(c) for c in codes])
        if exn:
            print(proj, file, exn, src_len - codes_len)
            if len(codes) > 4:
                print(' '.join(codes[-4]))
    return extract_proofs(codes)
    

def is_theorem(code: str, strict=True):
    if strict:
        return code.startswith('Theorem') or code.startswith('Lemma')
    else:
        for df in ['Theorem', 'Lemma', 'Example', 'Definition', 'Let', 'Corollary', 'Fixpoint', 'Instance', 'Goal', 'Remark', 'Fact']:
            if code.startswith(df):
                return True
        return False



def is_proof_begin(code: str):
    return code.startswith('Proof')


def is_proof_end(code: str):
    for end in ['Qed', 'Abort', 'Admitted', 'Defined']:
        if code.startswith(end) and code.endswith('.'):
            return True


def get_theorem_name(code: str, bp: int):
    code = code.replace('\n', ' ')
    if code.startswith('Goal'):
        return 'Goal', 'Goal_'+str(bp)
    ind1, ind2 = code.find(':'), code.find('(')
    ind1 = ind1 if ind1 >= 0 else len(code)
    ind2 = ind2 if ind2 >= 0 else len(code) 
    index = min(ind1, ind2)
    code = code[:index].strip()
    parts = code.split()
    # assert len(parts) == 2
    if code.startswith('Program Definition'):
        return 'Program Definition', parts[2].strip()
    return parts[0].strip(), parts[1].strip()


def extract_proofs(codes):
    ind = 0
    theorems = []
    while ind < len(codes):
        code = codes[ind]
        if is_theorem(code, False) or is_proof_begin(code):
            if is_theorem(code, False):
                if ind + 1 >= len(codes):
                    return codes, theorems
                if is_proof_begin(codes[ind+1]):
                    ind += 1
                    continue
                else:
                    kind, name = get_theorem_name(code, ind)
                    record = {'name': name, 'kind': kind, 'begin': ind, 'end': -1}
            else:
                if not is_theorem(codes[ind-1], False):
                    ind += 1
                    continue
                kind, name = get_theorem_name(codes[ind-1], ind-1)
                record = {'name': name, 'kind': kind, 'begin': ind-1, 'end': -1}

            found = False
            ind += 1
            while ind < len(codes):
                code_ = codes[ind]
                if is_proof_end(code_):
                    found = True
                    break
                elif is_theorem(code_, False) or is_proof_begin(code_):
                    break
                ind += 1
            if ind >= len(codes):
                return codes, theorems
            if found:
                record['end'] = ind
                theorems.append(record)
            else:
                ind -= 1
        ind += 1

    return codes, theorems


def work(file: str, proj: str, proj_path: str, skip):
    out_path = os.path.join(data_path, proj, change_post(file, 'json', 'v'))
    if skip and os.path.exists(out_path):
        return
    create_dir(out_path)
    codes, theorems = extract_file(proj, os.path.join(proj_path, file))
    json.dump({'code': codes, 'theorems': theorems}, open(out_path, 'w'))
    print(file, 'extracted:', len(theorems), 'theorems')
    return len(theorems)


def extract_projct(proj: str, threads=1, skip=False):
    total = 0
    proj_path = os.path.join(projects_path, proj)
    files = [f for f in files_in_rec(proj_path) if f.endswith('.v')]
    if threads > 1:
        files = [(f, proj, proj_path, skip) for f in files]
        pool = multiprocessing.Pool(processes=threads)
        pool.starmap(work, files)
        pool.close()
        pool.join()
    else:
        for f in files:
            out_path = os.path.join(data_path, proj, change_post(f, 'json', 'v'))
            if skip and os.path.exists(out_path):
                continue
            create_dir(out_path)
            codes, theorems = extract_file(proj, os.path.join(proj_path, f))
            json.dump({'code': codes, 'theorems': theorems}, open(out_path, 'w'))
            total += len(theorems)
    print(proj, 'extracted:', total, 'theorems')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--proj', type=str)
    parser.add_argument('--threads', default=1, type=int)
    args = parser.parse_args()
    extract_projct(args.proj, args.threads)
