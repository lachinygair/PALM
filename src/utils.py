import re
import os
import json
from .re_patterns import *
from .config import *
import numpy as np
import tiktoken
from collections import defaultdict
from pathlib import Path


def change_post(path: str, after: str, before=''):
    path = path.strip()
    if before == '':
        before = path.split('.')[-1]
    return path[:path.rfind('.'+before)]+'.'+after


def dirs_in(directory):
    dirs_all = []
    for item in os.listdir(directory):
        full_path = os.path.join(directory, item)
        if os.path.isdir(full_path):
            dirs_all.append(item)
    return dirs_all


def files_in_rec(directory):
    all_files = []
    for dirpath, dirnames, filenames in os.walk(directory):
        for filename in filenames:
            full_path = os.path.join(dirpath, filename)
            relative_path = os.path.relpath(full_path, directory)
            all_files.append(relative_path)
    return all_files


def remove_comments_file(in_file: str, out_file: str=None):
    comment = r'\(\*.*?\*\)'
    with open(in_file) as f:
        content = f.read()
        content = re.sub(comment, '', content, flags=re.DOTALL)
        all_lines = [line+'\n' for line in content.split('\n') if line.strip()]
    if out_file is None:
        name, post = in_file.split('.')
        out_file = name + '_no_comments.' + post
    with open(out_file , mode='w') as f:
        f.writelines(all_lines)


def remove_comments(code: str) -> str:
    if code == '':
        return ''
    characters = []
    num_left = 0
    in_string = False

    i = 0
    while i < len(code) - 1:
        if code[i] == '"':
            in_string = not in_string
        if not in_string and code[i : i + 2] == "(*":
            num_left += 1
            i += 2
        elif not in_string and num_left > 0 and code[i : i + 2] == "*)":
            num_left -= 1
            i += 2
        elif num_left == 0:
            characters.append(code[i])
            i += 1
        else:
            i += 1

    characters.append(code[-1])
    code_without_comment = "".join(characters)

    return code_without_comment


def remove_braces(s):
    pattern = r'\([^()]*\)'
    while re.search(pattern, s):
        s = re.sub(pattern, '', s)
    return s


def normalize_spaces(s: str) -> str:
    return re.sub(r"\s+", " ", s, flags=re.DOTALL)


def extract_qualids(expr):
    no = set(['_', 'Proof', 'using', 'Qed', 'destruct', 'left', 'right', 'reflexivity', 'unfold', 'simpl', 'intuition', 'induction',\
              'eauto', 'split', 'repeat', 'subst', 'intros', 'apply', 'forall', 'exists', 'rewrite', 'fun', 'Prop', 'Inductive', 'Type', 'Set'])
    pattern = r"\b[A-Za-z_][A-Za-z0-9_']*[^\w']"
    matches = re.findall(pattern, expr)
    return [m[:-1] for m in matches if m[:-1] not in no]


def prepare(file: str):
    file_full_path = os.path.join(data_path, file)
    proj = Path(file).parts[0]
    if not file_full_path.endswith('json'):
        file_full_path = change_post(file_full_path, 'json')
    with open(file_full_path) as f:
        data = json.load(f)
    with open(os.path.join(data_path, 'path.json')) as f:
        data_ = json.load(f)
        options, version = data_[proj]
        options = [op.strip() for op in options.split()]
        path_option = ''
        for i, option in enumerate(options):
            if i % 3 == 1:
                path_option += os.path.join(projects_path, proj, option) + ','
            else:
                path_option += option + ' '


    return data['code'], path_option, version, data['theorems']


def log(project: str, proof: str, succ: bool, record: str):
    if project.endswith('.v'):
        project = project[:-1]+'json'
    project = os.path.join('logs', project)
    if not os.path.exists(project):
        os.makedirs(os.path.dirname(project), exist_ok=True)
        with open(project, 'w') as f:
            json.dump({}, f)
    with open (project, mode='r+') as f:
        data = json.load(f)
        new = {'succ': succ, 'proof': record}
        if proof not in data:
            data[proof] = [new]
        else:
            data[proof].append(new)
        f.seek(0)
        json.dump(data, f)
        f.truncate()


indicators = ['-', '+', '*']


def compare_indicator(ind1: str, ind2: str):
    if ind1 == ind2:
        return 0
    if len(ind1) < len(ind2):
        return -1
    elif len(ind2) < len(ind1):
        return 1
    else:
        return indicators.index(ind1[0]) - indicators.index(ind2[0])
    

def indicator_level(indicator: str):
    if not is_indicator(indicator):
        return -1
    indi = indicator[0]
    length = len(indicator)
    return indicators.index(indi) + (length - 1) * 3


def is_indicator(indicator: str):
    return all(char == '-' for char in indicator) \
            or all(char == '+' for char in indicator) \
            or all(char == '*' for char in indicator)


def next_indicator_litera(indicator: str):
    if indicator == '':
        return '-'
    if not is_indicator(indicator):
        return ''
    else:
        indi = indicator[0]
        length = len(indicator)
        if indi == '-':
            return '+'*length
        elif indi == '+':
            return '*'*length
        else:
            return '-'*(length+1)
        

def move_indicator(indicator: str, times: int):
    if not is_indicator(indicator):
        return ''
    if times > 0:
        for _ in range(times):
            indicator = next_indicator_litera(indicator)
        return indicator
    else:
        return indicator


def extract_id(sexpr: str):
    pattern = r'\(Id ([a-zA-Z_\']+)\)'
    matches = re.findall(pattern, sexpr)
    return matches


def in_std(locate: str):
    return 'Coq.' in locate
    # tp, path = locate.split()
    # if path.startswith('Coq.'):
    #     return True
    # return False


def same_dict(dict1: dict, dict2: dict):
    if len(dict1) != len(dict2):
        return False
    for k in dict1.keys():
        if k not in dict2 or dict1[k] != dict2[k]:
            return False
    return True


def topk(numbers, k):
    arr = np.array(numbers)
    sorted_indices = np.argsort(arr)[::-1]
    topk_indices = sorted_indices[:k]
    return topk_indices, sorted_indices


def sorted_index(nums):
    indexed_nums = enumerate(nums)
    sorted_pairs = sorted(indexed_nums, key=lambda x: x[1], reverse=True)
    sorted_indices = [index for index, num in sorted_pairs]

    return sorted_indices


def process_apply(cmd: str):
    pattern = r"(apply|exact|rewrite)\s*\(?([a-zA-Z_][.a-zA-Z0-9'_]*)."
    matches = re.findall(pattern, cmd)
    return [match[1] for match in matches]


def create_dir(file_path: str):
    out_dir = file_path[:file_path.rfind('/')]
    if not os.path.exists(out_dir):
        os.makedirs(out_dir)


def iter_coq_files(coq_files, callback, proj_callback=None, get_data=True):
    projs = defaultdict(list)
    for file in coq_files:
        projs[get_proj(file)].append(file)

    i = 0
    for proj, files in projs.items():
        if proj_callback is not None:
            proj_callback(proj)
        for file in files:
            if get_data:
                with open(file) as f:
                    file_data = json.load(f)
                callback(file, file_data)
            else:
                callback(file)
            i += 1


def get_proj(file):
    parts = Path(file).parts
    i = len(parts) - 1
    while i > -1 and parts[i] != 'data':
        i -= 1
    return parts[i + 1]


def get_rel_path(file):
    parts = Path(file).parts
    i = len(parts) - 1
    while i > -1 and parts[i] != 'data':
        i -= 1
    return os.path.join(*(parts[i + 1:]))


def trim_prompt(prompt, limit=-1):
    encoding = tiktoken.encoding_for_model("gpt-3.5-turbo")
    encode = encoding.encode(prompt)
    if limit < 0:
        return len(encode), None
    else:
        return len(encode), encoding.decode(encode[:limit])
    

def trim_theorem(theorem: str, limit: int):
    limit -= 1
    sp = split_theorem(theorem)
    sp = [(s, trim_prompt(s)[0]) for s in sp]
    if len(sp) < 2:
        length, trim = trim_prompt(theorem, limit)
        return length + 1, trim + ('...' if length > limit else '')
    if sp[0][1] + sp[-1][1] > limit:
        return limit, trim_prompt(theorem, limit-1)[1] + '...'
    parts = [sp[0][0]]
    total = sp[0][1] + sp[-1][1]
    for s in sp[1:-1]:
        if total + s[1] > limit:
            break
        total += s[1] + 1
        parts.append(s[0])
    if len(parts) + 1 < len(sp):
        res = ' -> '.join(parts) + ' ->...-> ' + sp[-1][0]
    else:
        res = ' -> '.join(parts) + ' -> ' + sp[-1][0]
    return trim_prompt(res)[0], res
    

def split_theorem(theorem: str):
    parts = []  # To store the split parts
    current_part = []  # To build the current part
    parentheses_depth = 0  # To track the depth of nested parentheses
    i = 0 
    while i < len(theorem):
        char = theorem[i]
        if char == '(':
            parentheses_depth += 1
            current_part.append(char)
        elif char == ')':
            parentheses_depth -= 1
            current_part.append(char)
        elif char == '-' and i + 1 < len(theorem) and theorem[i + 1] == '>' and parentheses_depth == 0:
            parts.append(''.join(current_part).strip())
            current_part = []
            i += 1 
        else:
            current_part.append(char)
        i += 1 

    if current_part:
        parts.append(''.join(current_part).strip())
    return parts


if __name__ == '__main__':
    pass
