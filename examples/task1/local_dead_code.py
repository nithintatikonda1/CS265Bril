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
                unused = {}
                indices_to_remove = set()
                for index, instr in enumerate(block):
                    if 'args' in instr:
                        for use in instr['args']:
                            if use in unused:
                                del unused[use]
                    if 'dest' in instr:
                        if instr['dest'] in unused:
                            indices_to_remove.add(unused[instr['dest']])
                            converged = False
                        unused[instr['dest']] = index
                new_block = []
                for i in range(len(block)):
                    if i not in indices_to_remove:
                        new_block.append(block[i])
                new_instrs.extend(new_block)
            fn["instrs"] = new_instrs
            
    json.dump(prog, sys.stdout, indent=2)
