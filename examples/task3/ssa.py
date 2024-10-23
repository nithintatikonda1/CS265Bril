import json
import sys

TERMINATORS = 'br', 'jmp', 'ret'

from collections import OrderedDict
import itertools
from collections import deque


def flatten(ll):
    """Flatten an iterable of iterable to a single list.
    """
    return list(itertools.chain(*ll))


def fresh(seed, names):
    """Generate a new name that is not in `names` starting with `seed`.
    """
    i = 1
    while True:
        name = seed + str(i)
        if name not in names:
            return name
        i += 1


def block_map(blocks):
    """Given a sequence of basic blocks, which are lists of instructions,
    produce a `OrderedDict` mapping names to blocks.

    The name of the block comes from the label it starts with, if any.
    Anonymous blocks, which don't start with a label, get an
    automatically generated name. Blocks in the mapping have their
    labels removed.
    """
    by_name = OrderedDict()

    for block in blocks:
        # Generate a name for the block.
        if 'label' in block[0]:
            # The block has a label. Remove the label but use it for the
            # block's name.
            name = block[0]['label']
            block = block[1:]
        else:
            # Make up a new name for this anonymous block.
            name = fresh('b', by_name)

        # Add the block to the mapping.
        by_name[name] = block

    return by_name

def successors(instr):
    """Get the list of jump target labels for an instruction.

    Raises a ValueError if the instruction is not a terminator (jump,
    branch, or return).
    """
    if instr['op'] in ('jmp', 'br'):
        return instr['labels']
    elif instr['op'] == 'ret':
        return []  # No successors to an exit block.
    else:
        raise ValueError('{} is not a terminator'.format(instr['op']))


def add_terminators(blocks):
    """Given an ordered block map, modify the blocks to add terminators
    to all blocks (avoiding "fall-through" control flow transfers).
    """
    for i, block in enumerate(blocks.values()):
        if not block:
            if i == len(blocks) - 1:
                # In the last block, return.
                block.append({'op': 'ret', 'args': []})
            else:
                dest = list(blocks.keys())[i + 1]
                block.append({'op': 'jmp', 'labels': [dest]})
        elif block[-1]['op'] not in TERMINATORS:
            if i == len(blocks) - 1:
                block.append({'op': 'ret', 'args': []})
            else:
                # Otherwise, jump to the next block.
                dest = list(blocks.keys())[i + 1]
                block.append({'op': 'jmp', 'labels': [dest]})


def add_entry(blocks):
    """Ensure that a CFG has a unique entry block with no predecessors.

    If the first block already has no in-edges, do nothing. Otherwise,
    add a new block before it that has no in-edges but transfers control
    to the old first block.
    """
    first_lbl = next(iter(blocks.keys()))

    # Check for any references to the label.
    for instr in flatten(blocks.values()):
        if 'labels' in instr and first_lbl in instr['labels']:
            break
    else:
        return

    # References exist; insert a new block.
    new_lbl = fresh('entry', blocks)
    blocks[new_lbl] = []
    blocks.move_to_end(new_lbl, last=False)


def edges(blocks):
    """Given a block map containing blocks complete with terminators,
    generate two mappings: predecessors and successors. Both map block
    names to lists of block names.
    """
    preds = {name: [] for name in blocks}
    succs = {name: [] for name in blocks}
    for name, block in blocks.items():
        try:
            for succ in successors(block[-1]):
                succs[name].append(succ)
                preds[succ].append(name)
        except IndexError:
            pass
    return preds, succs


def reassemble(blocks):
    """Flatten a CFG into an instruction list."""
    # This could optimize slightly by opportunistically eliminating
    # `jmp .next` and `ret` terminators where it is allowed.
    instrs = []
    for name, block in blocks.items():
        instrs.append({'label': name})
        instrs += block
    return instrs



def form_blocks(instrs):
    """Given a list of Bril instructions, generate a sequence of
    instruction lists representing the basic blocks in the program.

    Every instruction in `instr` will show up in exactly one block. Jump
    and branch instructions may only appear at the end of a block, and
    control can transfer only to the top of a basic block---so labels
    can only appear at the *start* of a basic block. Basic blocks may
    not be empty.
    """

    # Start with an empty block.
    cur_block = []

    for instr in instrs:
        if 'op' in instr:  # It's an instruction.
            # Add the instruction to the currently-being-formed block.
            cur_block.append(instr)

            # If this is a terminator (branching instruction), it's the
            # last instruction in the block. Finish this block and
            # start a new one.
            if instr['op'] in TERMINATORS:
                yield cur_block
                cur_block = []

        else:  # It's a label.
            # End the block here (if it contains anything).
            if cur_block:
                yield cur_block

            # Start a new block with the label.
            cur_block = [instr]

    # Produce the final block, if any.
    if cur_block:
        yield cur_block

def union_sets(sets):
    unioned_set = set()
    for sett in sets:
        for elem in sett:
            unioned_set.add(elem)
    return unioned_set

def intersect_sets(sets):
    if len(sets) == 0:
        return set()
    elif len(sets) == 1:
        return sets[0].copy()
    else:
        return sets[0].intersection(intersect_sets(sets[1:]))

def should_keep(instr):
    # not all instructions have an 'op' field, like labels
    if "op" not in instr:
        return True
    return instr["op"] != "nop"

def topological_labels(block_mapping, succs):  
    def postorder(block_mapping, succs, explored, post, label):
        if label in explored:
            return
        explored.add(label)
        for next_label in succs[label]:
            postorder(block_mapping, succs, explored, post, next_label)

        post.append(label)
        
    explored = set()
    post = []
    postorder(block_mapping, succs, explored, post, next(iter(block_mapping.keys())))
    post.reverse()
    return post

def dominators(block_mapping, preds, succs):
    topological = topological_labels(block_mapping, succs)
    dominated_by = {}

    for label in topological:
        sets = []
        for pred_label in preds[label]:
            if pred_label in dominated_by:
                sets.append(dominated_by[pred_label])
        dominated_by_set = intersect_sets(sets)

        dominated_by_set.add(label)

        dominated_by[label] = dominated_by_set



    dominators_mapping = {}
    for key, vals in dominated_by.items():
        for val in vals:
            if val not in dominators_mapping:
                dominators_mapping[val] = set()
            dominators_mapping[val].add(key)

    return dominators_mapping

def dominance_tree(dominators_mapping):
    import copy
    strict_dominators_mapping = copy.deepcopy(dominators_mapping)
    for key in strict_dominators_mapping:
        strict_dominators_mapping[key].remove(key)
    tree = strict_dominators_mapping.copy()

    for dom in strict_dominators_mapping:
        indirect_subs = set()

        subs = strict_dominators_mapping[dom]
        for sub in subs:
            indirect_subs = union_sets([strict_dominators_mapping[sub], indirect_subs])

        for indirect_sub in indirect_subs:
            if indirect_sub in tree[dom]:
                tree[dom].remove(indirect_sub)
    return tree



def dominance_frontier(dominators_mapping, succs):
    frontier_map = {}
    for label in dominators_mapping:
        frontier = set()
        explored = set()
        dominators_set = dominators_mapping[label]
        
        queue = deque([label])
        while len(queue) != 0:
            curr_label = queue.popleft()
            if curr_label in explored:
                continue
            explored.add(curr_label)
            for next_label in succs[curr_label]:
                if next_label not in dominators_set or next_label == label:
                    frontier.add(next_label)
                if next_label in dominators_set:
                    queue.append(next_label)
        frontier_map[label] = frontier

    return frontier_map

def defining_blocks(block_mapping):
    defining_block_map = {}
    for label, block in block_mapping.items():
        for inst in block:
            if "dest" in inst:
                if inst['dest'] not in defining_block_map:
                    defining_block_map[inst['dest']] = set()
                defining_block_map[inst["dest"]].add(label)
    return defining_block_map

def variable_types(block_mapping):
    defining_block_map = {}
    types = {}
    for label, block in block_mapping.items():
        for inst in block:
            if "dest" in inst:
                if inst['dest'] not in defining_block_map:
                    defining_block_map[inst['dest']] = set()
                defining_block_map[inst["dest"]].add(label)
                types[inst["dest"]] = inst["type"]
    return types

var_num = {}
def fresh_name(var):
    if var not in var_num:
        var_num[var] = -1
    var_num[var] += 1
    return var + '___' + str(var_num[var])

def rename(block_mapping, label, dom_tree, stack):
    #print(label, stack, '\n')
    import copy
    block = block_mapping[label]
    stack = copy.deepcopy(stack)


    for inst in block:
        if 'args' in inst and  inst['op'] != 'phi':
            inst['args'] = [stack[arg][-1] if arg in stack else arg for arg in inst['args']]
        if 'dest' in inst:
            fresh = fresh_name(inst['dest'])
            if inst['dest'] not in stack:
                stack[inst['dest']] = []
            stack[inst['dest']].append(fresh)
            inst['dest'] = fresh
    for succ_block_label in succs[label]:
        for inst in block_mapping[succ_block_label]:
            if 'op' in inst and inst['op'] == 'phi':
                v = inst['dest']
                if len(v) >= 4 and '___' in v:
                    v = v.split('___')[0]
                for i in range(len(inst['labels'])):
                    if inst['labels'][i] == label:
                        inst['args'][i] = stack[v][-1] if v in stack else 'dummy'
    for child in dom_tree[label]:
        rename(block_mapping, child, dom_tree, stack)

    

if __name__ == "__main__":
    prog = json.load(sys.stdin)
    for fn in prog["functions"]:
        blocks = form_blocks(fn["instrs"])
        block_mapping = block_map(blocks)
        add_terminators(block_mapping)
        add_entry(block_mapping)
        preds, succs = edges(block_mapping)
        first_lbl = next(iter(block_mapping.keys()))


        dominance_map = dominators(block_mapping, preds, succs)
        dominance_frontier_map = dominance_frontier(dominance_map, succs)
        defining_block_map = defining_blocks(block_mapping)
        variables = defining_block_map.keys()
        types = variable_types(block_mapping)

        for var in variables:
            inserted_phi = set()

            defining_block_queue = deque(list(defining_block_map[var]))
            while len(defining_block_queue) != 0:
                defining_block = defining_block_queue.popleft()
                if defining_block not in dominance_frontier_map:
                    continue
                for block_label in dominance_frontier_map[defining_block]:
                    phi_function = phi = {
                            'op': 'phi',
                            'dest': var,
                            'type': types[var],
                            'labels': [label for label in preds[block_label]],
                            'args': [var for _ in preds[block_label]]
                        }
                    if block_label not in inserted_phi:
                        block_mapping[block_label].insert(0, phi_function)
                        defining_block_map[var].add(block_label)
                        defining_block_queue.append(block_label)
                        inserted_phi.add(block_label)

        dom_tree = dominance_tree(dominance_map)

        stack = {}
        if 'args' in fn:
            for arg in fn['args']:
                stack[arg['name']] = [arg['name']]
        rename(block_mapping, first_lbl, dom_tree, stack)

        #Rewrite program using updated blocks
        instrs = []
        for label, block in block_mapping.items():
            instrs.append({'label': label})
            instrs += block
        fn['instrs'] = instrs

    json.dump(prog, sys.stdout, indent=2)