import click
import tomlkit
import subprocess
import re
import csv
import sys


def run_pipe(cmds, input):
    last_proc = None
    for i, cmd in enumerate(cmds):
        proc = subprocess.Popen(
            cmd,
            shell=True,
            text=True,
            stdin=last_proc.stdout if last_proc else subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
                   if i == len(cmds) - 1 else subprocess.DEVNULL,
        )
        if not last_proc:
            first_proc = proc
        last_proc = proc

    # Send stdin and collect stdout.
    first_proc.stdin.write(input)
    first_proc.stdin.close()
    return last_proc.communicate()


@click.command()
@click.option('-c', '--config', 'config_path',
              nargs=1, type=click.Path(exists=True))
@click.argument('file', nargs=-1, type=click.Path(exists=True))
def brench(config_path, file):
    with open(config_path) as f:
        config = tomlkit.loads(f.read())

    extract_re = re.compile(config['extract'])

    # CSV for collected outputs.
    writer = csv.writer(sys.stdout)
    writer.writerow(['run', 'benchmark', 'result'])

    for name, run in config['runs'].items():
        cmds = [
            c.format(args='5')
            for c in run['pipeline']
        ]
        for fn in file:
            with open(fn) as f:
                in_data = f.read()
            stdout, stderr = run_pipe(cmds, in_data)

            # Look for results.
            result = None
            for out in stdout, stderr:
                match = extract_re.search(out)
                if match:
                    result = match.group(1)
                    break

            writer.writerow([name, fn, result or ''])


if __name__ == '__main__':
    brench()
