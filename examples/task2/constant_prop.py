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

def intersect_dicts(dicts):
    import copy
    if not dicts:
        return {}
    common_items = copy.deepcopy(dicts[0])
    for d in dicts[1:]:
        common_items = {k: v for k, v in common_items.items() if k in d and d[k] == v}
    return dict(common_items)

def should_keep(instr):
    # not all instructions have an 'op' field, like labels
    if "op" not in instr:
        return True
    return instr["op"] != "nop"



if __name__ == "__main__":
    prog = json.load(sys.stdin)
    converged = False
    while not converged:
        converged = True
        for fn in prog["functions"]:
            changed = False
            blocks = form_blocks(fn["instrs"])
            block_mapping = block_map(blocks)
            add_terminators(block_mapping)
            add_entry(block_mapping)
            preds, succs = edges(block_mapping)
            first_lbl = next(iter(block_mapping.keys()))
            queue = deque([first_lbl])
            info_mapping = {}
            for label in block_mapping.keys():
                info_mapping[label] = {}

            while len(queue) > 0:
                label = queue.popleft()
                block = block_mapping[label]


                old_info = info_mapping[label]
                info = {}
                if len(preds[label]) > 0:
                    info = intersect_dicts([info_mapping[p] for p in preds[label]])

                info_mapping[label] = info
                
                for inst in block:
                    if 'op' not in inst or inst['op'] in TERMINATORS or inst['op'] == 'alloc' or inst['op'] == 'call':
                        continue
                    if inst['op'] == 'const':
                        if 'dest' in inst:
                            info[inst['dest']] = inst['value']
                    if 'args' in inst:
                        #Check if all args are in info
                        known = True
                        for arg in inst['args']:
                            if arg not in info:
                                known = False
                                break
                    
                        if known:
                            changed = True
                            if inst['op'] == 'add':
                                inst['value'] = info[inst['args'][0]] + info[inst['args'][1]]
                                inst['op'] = 'const'
                                del inst['args']
                            elif inst['op'] == 'mul':
                                inst['value'] = info[inst['args'][0]] * info[inst['args'][1]]
                                inst['op'] = 'const'
                                del inst['args']
                            elif inst['op'] == 'sub':
                                inst['value'] = info[inst['args'][0]] - info[inst['args'][1]]
                                inst['op'] = 'const'
                                del inst['args']
                            elif inst['op'] == 'eq':
                                inst['value'] = info[inst['args'][0]] == info[inst['args'][1]]
                                inst['op'] = 'const'
                                del inst['args']
                            elif inst['op'] == 'lt':
                                inst['value'] = info[inst['args'][0]] < info[inst['args'][1]]
                                inst['op'] = 'const'
                                del inst['args']
                            elif inst['op'] == 'gt':
                                inst['value'] = info[inst['args'][0]] > info[inst['args'][1]]
                                inst['op'] = 'const'
                                del inst['args']
                            elif inst['op'] == 'le':
                                inst['value'] = info[inst['args'][0]] <= info[inst['args'][1]]
                                inst['op'] = 'const'
                                del inst['args']
                            elif inst['op'] == 'ge':
                                inst['value'] = info[inst['args'][0]] >= info[inst['args'][1]]
                                inst['op'] = 'const'
                                del inst['args']
                            elif inst['op'] == 'and':
                                inst['value'] = info[inst['args'][0]] and info[inst['args'][1]]
                                inst['op'] = 'const'
                                del inst['args']
                            elif inst['op'] == 'or':
                                inst['value'] = info[inst['args'][0]] or info[inst['args'][1]]
                                inst['op'] = 'const'
                                del inst['args']
                            elif inst['op'] == 'not':
                                inst['value'] = not info[inst['args'][0]]
                                inst['op'] = 'const'
                                del inst['args']
                            elif inst['op'] == 'id':
                                inst['op'] = 'const'
                                inst['value'] = info[inst['args'][0]]
                                del inst['args']
                            else:
                                changed = False

                            if 'dest' in inst and changed:
                                converged = False
                                info[inst['dest']] = inst['value']

                info_mapping[label] = info

                #Check if old info and new info are the same
                if old_info != info:
                    queue.extend(succs[label])

    json.dump(prog, sys.stdout, indent=2)