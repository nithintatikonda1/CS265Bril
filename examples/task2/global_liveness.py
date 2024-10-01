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
    import copy
    unioned_set = set()
    for sett in sets:
        for elem in sett:
            unioned_set.add(elem)
    return unioned_set

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
            last_labels = []
            for label in block_mapping.keys():
                if len(succs[label]) == 0:
                    last_labels.append(label)
            queue = deque(last_labels)
            info_mapping = {}

            #Initialize all variables to be live (pessimistically)
            liveness = set()
            for inst in fn["instrs"]:
                if 'args' in inst:
                    for arg in inst['args']:
                        liveness.add(arg)
            for label in block_mapping.keys():
                info_mapping[label] = liveness

            while len(queue) > 0:
                label = queue.popleft()
                block = block_mapping[label]


                old_info = info_mapping[label]
                info = set()
                if len(succs[label]) > 0:
                    info = union_sets([info_mapping[s] for s in succs[label]])

                info_mapping[label] = info

                for inst in reversed(block):
                    if 'dest' in inst and inst['dest'] in info:
                        info.remove(inst['dest'])
                    elif 'dest' in inst:
                        inst.clear()
                        inst['op'] = 'nop'
                        converged = False
                        continue

                    if 'args' in inst:
                        for arg in inst['args']:
                            info.add(arg)

                info_mapping[label] = info

                predecessors = preds[label]
                if old_info != info:
                    queue.extend(predecessors)

    for fn in prog["functions"]:
        fn["instrs"] = [instr for instr in fn["instrs"] if should_keep(instr)]
    json.dump(prog, sys.stdout, indent=2)