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



def rename(block_mapping, label, dom_tree, stack):
    #print(label, stack, '\n')
    import copy
    block = block_mapping[label]
    stack = copy.deepcopy(stack)

var_num = {}
def fresh_name(var):
    if var not in var_num:
        var_num[var] = -1
    var_num[var] += 1
    return var + '____' + str(var_num[var])


def loop_block(label, succs, header, tails, explored):
    if label in explored:
        return False
    explored.add(label)
    if label == header:
        return False
    if label in tails:
        return True
    for next_label in succs[label]:
        if loop_block(next_label, succs, header, tails, explored):
            return True
    return False
    

    

if __name__ == "__main__":
    prog = json.load(sys.stdin)
    for fn in prog["functions"]:
        blocks = form_blocks(fn["instrs"])
        block_mapping = block_map(blocks)
        add_terminators(block_mapping)
        preds, succs = edges(block_mapping)
        first_lbl = next(iter(block_mapping.keys()))


        dominance_map = dominators(block_mapping, preds, succs)

        #Find backedges
        queue = deque([first_lbl])
        back_edges = set()
        explored = set()
        while len(queue) != 0:
            curr_label = queue.popleft()
            if curr_label in explored:
                continue
            explored.add(curr_label)
            for next_label in succs[curr_label]:
                if curr_label in dominance_map[next_label]:
                    back_edges.add((curr_label, next_label))
                if next_label not in explored:
                    queue.append(next_label)



        # Find all backedges with the same header
        # Also create preheader names
        header_to_tails = {}
        header_to_preheader = {}
        for backedge in back_edges:
            header = backedge[1]
            tail = backedge[0]
            if header not in header_to_tails:
                header_to_tails[header] = set()
            if header not in header_to_preheader:
                header_to_preheader[header] = fresh_name("preheader")
            header_to_tails[header].add(tail)


        # Find list of nodes associated with each header
        header_to_loop_labels = {}
        for header in header_to_tails:
            if header not in header_to_loop_labels:
                header_to_loop_labels[header] = set([header])
            for label in block_mapping:
                if loop_block(label, succs, header, header_to_tails[header], set()):
                    header_to_loop_labels[header].add(label)

        # Change jumps and branches to headers to jumps and branches to preheaders (if not in loop)
        for header, loop_labels in header_to_loop_labels.items():
            for label, block in block_mapping.items():
                if label not in loop_labels:
                    inst = block[-1]
                    if inst['op'] == 'jmp' and inst['labels'][0] == header:
                        inst['labels'][0] = header_to_preheader[header]
                    elif inst['op'] == 'br' and header in inst['labels']:
                        inst['labels'][inst['labels'].index(header)] = header_to_preheader[header]

        # Change labels in phi function to be from preheader
        for header in header_to_loop_labels:
            for inst in block_mapping[header]:
                if 'op' in inst and inst['op'] == 'phi':
                    for i in range(len(inst['labels'])):
                        if inst['labels'][i] not in header_to_loop_labels[header]:
                            inst['labels'][i] = header_to_preheader[header]

        # Find loop invariant code
        preheader_mapping = {}
        for header, loop_labels in header_to_loop_labels.items():
            defined_in_loop = set()

            for label in loop_labels:
                for inst in block_mapping[label]:
                    if 'dest' in inst:
                        defined_in_loop.add(inst['dest'])

            preheader_instrs = []
            for label in loop_labels:
                instrs = []
                for inst in block_mapping[label]:
                    if 'args' in inst and inst['op'] != 'br' and inst['op'] in ['add', 'sub', 'mul' , 'eq', 'lt', 'gt', 'le', 'ge', 'not', 'and', 'or', 'id']:
                        loop_invariant = True
                        for arg in inst['args']:
                            if arg in defined_in_loop:
                                loop_invariant = False
                                break
                        if not loop_invariant:
                            instrs.append(inst)
                        else:
                            preheader_instrs.append(inst)
                    elif 'op' in inst and inst['op'] == 'const':
                        preheader_instrs.append(inst)
                    else:
                        instrs.append(inst)
                block_mapping[label] = instrs
            preheader_mapping[header_to_preheader[header]] = preheader_instrs
                    


        # Reconstruct program inserting preheaders
        instrs = []
        for label, block in block_mapping.items():
            if label in header_to_preheader:
                instrs.append({'label': header_to_preheader[label]})
                if len(preheader_mapping[header_to_preheader[label]]) > 0:
                    instrs += preheader_mapping[header_to_preheader[label]]
                else:
                    instrs.append({'op': 'nop'})

            instrs.append({'label': label})
            instrs += block
        fn['instrs'] = instrs
            

    json.dump(prog, sys.stdout, indent=2)