import json
import sys


def should_keep(instr, used):
    # not all instructions have an 'op' field, like labels
    if "op" not in instr:
        return True
    if instr["op"] in ["ret", "jump", "print", "br", "ret"]:
        return True
    if instr["op"] == "nop":
        return False
    if "dest" in instr:
        return instr["dest"] in used
    return True

def get_used(prog):
    used = set()
    for fn in prog["functions"]:
        for instr in fn["instrs"]:
            if "args" in instr:
                for arg in instr["args"]:
                    used.add(arg)
    return used


if __name__ == "__main__":
    prog = json.load(sys.stdin)
    used = get_used(prog)
    for fn in prog["functions"]:
        fn["instrs"] = [instr for instr in fn["instrs"] if should_keep(instr, used)]
    json.dump(prog, sys.stdout, indent=2)
