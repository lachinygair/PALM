from .utils import *
    

class Node:
    def __init__(self, tactic: str, state_id: int, source='#') -> None:
        self.tactic = tactic
        self.state_id = state_id
        self.source = source


class List:
    def __init__(self) -> None:
        self.list = []
        self.exceptions = []
        self.cur = -1

    def __getitem__(self, key):
        return self.list[key]
    
    def __repr__(self):
        return repr(self.list)
    
    def __len__(self):
        return len(self.list)
    
    def index(self, node: Node):
        return self.list.index(node)
            
    def pop(self, index=-1):
        if index < 0:
            index = self.cur

        self.list.pop(index)
        if index == 0:
            self.cur = 0 if len(self.list) > 0 else -1
        else:
            self.cur = index - 1

    def insert(self, tactic: str, state_id: int, source='', index=-1):
        if index < 0:
            index = self.cur + 1
        self.list.insert(index, Node(tactic, state_id, source))
        self.cur = index

    def get_last_shelved(self):
        cur = None
        for index, node in enumerate(self.list):
            if node.tactic == 'shelve.':
                cur = node
        return cur, self.get_structure(self.index(cur)) if cur is not None else -1

    def get_structure(self, point=-1):
        if point < 0:
            point = self.cur
        res = []
        for node in self[:point+1]:
            tactic = node.tactic
            if is_indicator(tactic):
                if tactic in res:
                    res = res[:res.index(tactic)+1]
                else:
                    res.append(tactic)
        return res

    def cut_bullet(self, start=-1):
        if start < 0:
            start = self.cur
        bullet = self[start].tactic
        if not is_indicator(bullet):
            return
        structure = self.get_structure(start)

        first = start
        last = start
        # only one layer of bullets
        if len(structure) == 1:
            for idx, node in enumerate(self):
                if node.tactic == structure[-1]:
                    first = idx
                    break
            last = len(self) # - 1 
        # multiple layers
        else:
            index = start - 1
            last_bullet = structure[-2]
            while index >= 0:
                tactic = self[index].tactic
                if tactic == last_bullet:
                    break
                if tactic == bullet:
                    first = index
                index -= 1
        
            index = start + 1
            while index < len(self):
                tactic = self[index].tactic
                if tactic in structure[:-1]:
                    last = index
                    break
                index += 1
            if index >= len(self) and last == start:
                last = len(self)
        
        self.cur = first - 1
        self.list = self.list[:first] + self.list[last:]
    
    def get_shelved(self):
        return [(ind, node) for ind, node in enumerate(self.list) if 'shelve.' in node.tactic]
    
    # for indicators, back to position after them. for others, back to before them.
    def get_nodes(self, keywords, before_indicators=True):
        res = []
        for ind, node in enumerate(self.list):
            if before_indicators and is_indicator(node.tactic):
                res.append((ind, node))
            else:
                for kw in keywords:
                    if kw in node.tactic:
                        res.append((ind, node))
        return res

    def get_key_nodes(self):
        return self.get_nodes(['induction', 'destruct', 'unfold', 'intros'])
    
    def add_exn(self, tactic: str, exn: str, tp: str, handled=False):
        self.exceptions.append({'ctx': [n.tactic for n in self.list], 'tactic': tactic, 'exn': exn, 'type': tp, 'handled': handled})
    
    def as_list(self):
        return [n.tactic for n in self.list]
    
    def repairs(self):
        return [n.source for n in self.list]

    def log(self):
        return {'proof': ' '.join(self.as_list()), 'repairs': self.repairs(), 'exceptions': self.exceptions}
    