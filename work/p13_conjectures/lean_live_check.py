"""Persistent Lean LSP checker for a local file; CLI compilation remains final evidence.
Usage: LEAN_PATH="$PWD:$LEAN_PATH" lake env python3 lean_live_check.py File.lean
Commands on stdin: check, goal LINE, quit. LINE is one-based.
"""
import json
import subprocess
import sys
import threading
from pathlib import Path

path = Path(sys.argv[1]).resolve()
uri = path.as_uri()
proc = subprocess.Popen(['lean', '--server'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
lock = threading.Lock()
version = 1

def send(method, params, ident=None):
    msg = {'jsonrpc': '2.0', 'method': method, 'params': params}
    if ident is not None:
        msg['id'] = ident
    data = json.dumps(msg).encode()
    with lock:
        proc.stdin.write(f'Content-Length: {len(data)}\r\n\r\n'.encode() + data)
        proc.stdin.flush()

def read():
    while True:
        headers = {}
        while True:
            line = proc.stdout.readline()
            if not line:
                return
            if line == b'\r\n':
                break
            key, value = line.decode().split(':', 1)
            headers[key.lower()] = value.strip()
        msg = json.loads(proc.stdout.read(int(headers['content-length'])))
        if msg.get('id') == 1:
            send('initialized', {})
            send('textDocument/didOpen', {'textDocument': {'uri': uri,
                 'languageId': 'lean4', 'version': version, 'text': path.read_text()}})
        elif msg.get('method') == 'textDocument/publishDiagnostics':
            p = msg['params']
            print(json.dumps({'version': p.get('version'), 'diagnostics': [
                {'line': d['range']['start']['line']+1, 'severity': d.get('severity'),
                 'message': d['message']} for d in p['diagnostics']]}, ensure_ascii=False), flush=True)
        elif msg.get('method') == '$/lean/fileProgress':
            if not msg['params'].get('processing'):
                print('ELABORATION FINISHED', flush=True)
        elif 'id' in msg:
            print(json.dumps(msg, ensure_ascii=False), flush=True)

threading.Thread(target=read, daemon=True).start()
send('initialize', {'processId': None, 'rootUri': path.parent.as_uri(),
    'capabilities': {}, 'initializationOptions': {'hasWidgets': False, 'editDelay': 0}}, 1)
try:
    for line in sys.stdin:
        cmd = line.strip()
        if cmd == 'quit':
            break
        if cmd == 'check':
            version += 1
            send('textDocument/didChange', {'textDocument': {'uri': uri, 'version': version},
                'contentChanges': [{'text': path.read_text()}]})
            print(f'CHECK VERSION {version}', flush=True)
        elif cmd.startswith('goal '):
            send('$/lean/plainGoal', {'textDocument': {'uri': uri},
                'position': {'line': int(cmd.split()[1])-1, 'character': 2}}, 2)
finally:
    proc.terminate()
    proc.wait()
