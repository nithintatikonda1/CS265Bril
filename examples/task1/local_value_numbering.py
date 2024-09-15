import json
import sys

TERMINATORS = 'br', 'jmp', 'ret'


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


if __name__ == "__main__":
    prog = json.load(sys.stdin)
    converged = False
    while not converged:
        converged = True
        for fn in prog["functions"]:
            new_instrs = []
            for block in form_blocks(fn["instrs"]):
                val2num = {}
                num2val = {}
                var2num = {}
                num2var = {}
                number = 0
                for inst in block:
                    # canonicalize the instruction's arguments by getting the 
                    # value numbers currently held by those vars
                    if 'op' not in inst or inst['op'] in TERMINATORS or inst['op'] == 'alloc' or inst['op'] == 'id' or inst['op'] == 'call':
                        new_instrs.append(inst)
                        continue

                    value = None
                    if 'args' in inst:
                        args = [(var2num[arg] if arg in var2num else arg) for arg in inst['args']]
                        value = [inst['op']] + args
                    elif inst['op'] == 'const':
                        value = ['const'] + [inst['value']]

                    num = val2num.get(repr(value))

                    if num is None and 'dest' in inst:
                        num = number
                        val2num[repr(value)] = num
                        num2val[num] = value
                        number = number + 1
                    elif num != None and 'args' in inst:
                        inst['op'] = "id"
                        inst['args'] = [num2var[num][0]]
                        converged = False

                    if 'dest' in inst and inst['dest'] in var2num:
                        old_num = var2num[inst['dest']]
                        num2var[old_num].remove(inst['dest'])
                        if len(num2var[old_num]) == 0:
                            del num2var[old_num]
                            old_val = num2val[old_num]
                            del val2num[repr(old_val)]
                            del num2val[old_num]


                        var2num[inst['dest']] = num
                        if num not in num2var:
                            num2var[num] = []
                        num2var[num].append(inst['dest'])

                    elif 'dest' in inst:
                        var2num[inst['dest']] = num
                        if num not in num2var:
                            num2var[num] = []
                        num2var[num].append(inst['dest'])

                    new_instrs.append(inst)
            fn["instrs"] = new_instrs
            
    json.dump(prog, sys.stdout, indent=2)