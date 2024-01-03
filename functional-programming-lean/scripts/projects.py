import difflib
import json
import re
from pathlib import Path
import os
from pprint import pformat
import shlex
import shutil
import subprocess
import sys
import tempfile

def eprint(val):
    print(val, file=sys.stderr)

command_re = re.compile(r'\{\{#command\s+\{(?P<dir>[^}]+)\}\s*\{(?P<container>[^}]+)\}\s*\{(?P<command>[^}]+)\}\s*(\{(?P<show>[^}]+)\}\s*)?\}\}')
command_out_re = re.compile(r'\{\{#command_out\s+\{(?P<container>[^}]+)\}\s*\{(?P<command>[^}]+)\}\s*(\{(?P<expected>[^}]+)\}\s*)?\}\}')
file_contents_re = re.compile(r'\{\{#file_contents\s+\{(?P<container>[^}]+)\}\s*\{(?P<file>[^}]+)\}\s*(\{(?P<expected>[^}]+)\}\s*)?\}\}')


def mangle(string):
    return string.replace('-', '---').replace('/', '-slash-')

def diff(str1, str2):
    d = difflib.Differ()
    result = list(d.compare(str1.splitlines(keepends=True), str2.splitlines(keepends=True)))
    return pformat(result)

def ditch_cr(s):
    return s.replace('\r', '')

class ContainerContext:

    def __init__(self, project_root):
        self.project_root = project_root
        # A mapping from "container" names to working directories
        self.containers = {}
        self.outputs = {}

    def __enter__(self):
        return self

    def __exit__(self, typ, value, traceback):
        # delete all created containers
        for i in self.containers:
            self.containers[i].__exit__(typ, value, traceback)

    def lean_version(self):
        with open(f"{self.project_root}{os.path.sep}examples{os.path.sep}lean-toolchain", 'r') as f:
            return f.read().strip()

    def env_with_examples_path(self):
        new_env = os.environ.copy()
        new_env["PATH"] = f"{self.project_root}/examples/build/bin" + os.pathsep + new_env["PATH"]
        return new_env


    def ensure_container(self, name):
        if name not in self.containers:
            tmp = tempfile.TemporaryDirectory(prefix=mangle(name))
            self.containers[name] = tmp
            shutil.copytree(self.project_root, tmp.name, dirs_exist_ok=True, ignore=shutil.ignore_patterns('.*', '*~'))
            subprocess.run(["elan", "override", "set", self.lean_version()], cwd=tmp.name, check=True, capture_output=True)
        return self.containers[name].name

    def rewrite_command(self, project_root):
        def rewrite(found):
            container = found.group('container')
            container_dir = self.ensure_container(container)
            directory = found.group('dir')
            command = found.group('command')
            show = found.group('show')
            the_dir = f'{container_dir}{os.path.sep}examples{os.path.sep}{directory}'
            os.makedirs(the_dir, exist_ok=True)
            try:
                val = subprocess.run(command,
                                     shell=True,
                                     cwd=the_dir,
                                     check=True,
                                     # Interleave both stderr and stdout into the same place
                                     stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT,
                                     env=self.env_with_examples_path())
            except subprocess.CalledProcessError as e:
                eprint("Output:")
                eprint(e.output)
                eprint("Stderr:")
                eprint(e.stderr)
                raise e

            if container not in self.outputs: self.outputs[container] = {}
            self.outputs[container][command] = val.stdout.decode('utf-8')
            if show is None:
                return command
            else:
                return show

        return rewrite

    def rewrite_command_out(self, project_root):
        def rewrite(found):
            container = found.group('container')
            command = found.group('command')
            expect = found.group('expected')
            expected_output = None
            if expect is None:
                expected_output = None
            else:
                with open(f"{self.project_root}{os.path.sep}examples{os.path.sep}{expect}", 'r') as f:
                    expected_output = f.read()
            output = self.outputs[container][command].rstrip()
            if expected_output is not None:
                assert ditch_cr(output) == ditch_cr(expected_output.rstrip()), f'expected {command} in {self.project_root}{os.path.sep}examples{os.path.sep}{expect} to match actual:\n{output}\nDiff:\n{diff(expected_output, output)}'
            return output.rstrip()
        return rewrite

    def rewrite_file_contents(self, project_root):
        def rewrite(found):
            container = found.group('container')
            filename = found.group('file')
            expect = found.group('expected')
            expected_contents = None
            if expect is None:
                expected_contents = None
            else:
                with open(f"{self.project_root}{os.path.sep}examples{os.path.sep}{expect}", 'r') as f:
                    expected_contents = f.read()
            container_dir = self.ensure_container(container)
            with open(f'{container_dir}{os.path.sep}examples{os.path.sep}{filename}') as f:
                contents = f.read().rstrip()
                if expected_contents is not None:
                    assert contents == expected_contents.rstrip(), f'expected {self.project_root}{os.path.sep}examples{os.path.sep}{expect} matches actual:\n{contents}'
                return contents
        return rewrite

    def run_examples(self, context, book):
        project_root = Path(context['root']).parent
        def test_chapters(chapters):
            for ch in chapters:
                ch['Chapter']['content'] = command_re.sub(self.rewrite_command(project_root), ch['Chapter']['content'])
                ch['Chapter']['content'] = command_out_re.sub(self.rewrite_command_out(project_root), ch['Chapter']['content'])
                ch['Chapter']['content'] = file_contents_re.sub(self.rewrite_file_contents(project_root), ch['Chapter']['content'])
                test_chapters(ch['Chapter']['sub_items'])

        test_chapters(book['sections'])
        return book

def main():
    if len(sys.argv) > 1:
        if sys.argv[1] == "supports":
            sys.exit(0)
    context, book_contents = json.load(sys.stdin)
    with ContainerContext(Path(context['root']).parent) as ctx:
        print(json.dumps(ctx.run_examples(context, book_contents)))

if __name__ == '__main__':
    main()
