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

def union_dicts(dicts):
    import copy
    if not dicts:
        return {}
    unioned_dict = {}
    for d in dicts:
        for var, sett in d.items():
            if var in unioned_dict:
                unioned_dict[var] |= sett
            else:
                unioned_dict[var] = copy.deepcopy(sett)
    return dict(unioned_dict)

def should_keep(instr):
    # not all instructions have an 'op' field, like labels
    if "op" not in instr:
        return True
    return instr["op"] != "nop"

def mem_location(label, inst_num):
    #Generate unique name for intruction
    return label + "______" + str(inst_num)

def union_sets(sets):
    import copy
    unioned_set = set()
    for sett in sets:
        for elem in sett:
            unioned_set.add(elem)
    return unioned_set



if __name__ == "__main__":
    prog = json.load(sys.stdin)
    converged = False
    while not converged:
        converged = True
        for fn in prog["functions"]:

            # ALIAS ANALYSIS

            changed = False
            blocks = form_blocks(fn["instrs"])
            block_mapping = block_map(blocks)
            add_terminators(block_mapping)
            add_entry(block_mapping)
            preds, succs = edges(block_mapping)
            first_lbl = next(iter(block_mapping.keys()))
            queue = deque(list(block_mapping.keys()))
            info_mapping = {}
            for label in block_mapping.keys():
                info_mapping[label] = {}

            all_mem_locations = set()

            while len(queue) > 0:
                label = queue.popleft()
                block = block_mapping[label]


                old_info = info_mapping[label]
                info = {}
                if len(preds[label]) > 0:
                    info = union_dicts([info_mapping[p] for p in preds[label]])

                info_mapping[label] = info
                
                inst_num = 0
                for inst in block:
                    inst_num += 1

                    if 'op' in inst:
                        if inst['op'] == 'alloc':
                            if 'dest' in inst:
                                mem_location_id = mem_location(label, inst_num)
                                all_mem_locations.add(mem_location_id)
                                info[inst['dest']] = set([mem_location_id])

                        if inst['op'] == 'id' or inst['op'] == 'ptradd':
                            if 'dest' in inst:
                                if inst['args'][0] in info:
                                    info[inst['dest']] = info[inst['args'][0]].copy()
                        if inst['op'] == 'load':
                            if 'dest' in inst:
                                info[inst['dest']] = all_mem_locations.copy()


                info_mapping[label] = info

                #Check if old info and new info are the same
                if old_info != info:
                    queue.extend(succs[label])

            
            # DEAD STORE ELIMINATION

            last_labels = []
            for label in block_mapping.keys():
                if len(succs[label]) == 0:
                    last_labels.append(label)
            queue = deque(list(reversed(block_mapping.keys())))
            memory_mapping = info_mapping
            info_mapping = {} # For each block, store the possible memory locations that have been read from.
            store_mapping = {} # Stores variables that have been stored to. If variable changes i backward pass, then remove it.


            for label, block in block_mapping.items():
                info_mapping[label] = set()
                store_mapping[label] = set()

            for label in block_mapping.keys():
                if len(succs[label]) == 0:
                    queue.append(label)

            while len(queue) > 0:
                label = queue.popleft()
                block = block_mapping[label]

                old_info = info_mapping[label]
                old_store_info = store_mapping[label]
                store_info = set()
                info = set()
                if len(succs[label]) > 0:
                    info = union_sets([info_mapping[s] for s in succs[label]])
                    store_info = set.intersection(*[store_mapping[s].copy() for s in succs[label]])

                info_mapping[label] = info
                #print(label, info, store_info)

                for inst in reversed(block):
                    if 'op' in inst and (inst['op'] == 'load' or inst['op'] == 'ret') and 'args' in inst and len(inst['args']) > 0:
                        pointer = inst['args'][0]
                        if pointer in memory_mapping[label]:
                            info.update(memory_mapping[label][pointer])

                    if 'op' in inst and inst['op'] == 'store':
                        pointer = inst['args'][0]
                        if pointer in store_info:
                            #Check if the pointer aliases to any of the memory locations that have been read from
                            aliases = False
                            for alias in memory_mapping[label][pointer]:
                                if alias in info:
                                    aliases = True
                            if not aliases:
                                inst.clear()
                                inst['op'] = 'nop'
                        if pointer in memory_mapping[label] and len(memory_mapping[label][pointer]) == 1:
                            if list(memory_mapping[label][pointer])[0] in info:
                                info.remove(list(memory_mapping[label][pointer])[0])
                        store_info.add(pointer)
                        

                    if 'dest' in inst and inst['dest'] in store_info:
                        store_info.remove(inst['dest'])
 

                info_mapping[label] = info
                store_mapping[label] = store_info


                predecessors = preds[label]
                if old_info != info or old_store_info != store_info:
                    queue.extend(predecessors)

        
    for fn in prog["functions"]:
        fn["instrs"] = [instr for instr in fn["instrs"] if should_keep(instr)]
    json.dump(prog, sys.stdout, indent=2)