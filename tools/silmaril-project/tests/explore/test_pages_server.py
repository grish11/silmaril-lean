import pathlib, tempfile, subprocess, urllib.request, urllib.error, time, socket
server=str(pathlib.Path(__file__).with_name('pages_server.py'))
with tempfile.TemporaryDirectory() as tmp:
    base=pathlib.Path(tmp); root=base/'site'; root.mkdir(); sibling=base/'site-secret'; sibling.mkdir()
    (root/'index.html').write_text('public'); (sibling/'index.html').write_text('private'); (root/'escape').symlink_to(sibling, target_is_directory=True)
    with socket.socket() as sock:
        sock.bind(('127.0.0.1',0)); port=sock.getsockname()[1]
    proc=subprocess.Popen(['python3','-I',server,'--root',str(root),'--port',str(port),'--log',str(base/'requests')])
    try:
        for i in range(100):
            try:
                assert urllib.request.urlopen(f'http://127.0.0.1:{port}/').read()==b'public'; break
            except urllib.error.URLError: time.sleep(.02)
        for path in ['/../site-secret/index.html','/%2e%2e/site-secret/','/escape/','/escape/index.html']:
            try: urllib.request.urlopen(f'http://127.0.0.1:{port}'+path); raise AssertionError(path)
            except urllib.error.HTTPError as e: assert e.code==404
        (root/'new.json').write_text('new fixture')
        assert urllib.request.urlopen(f'http://127.0.0.1:{port}/new.json').read()==b'new fixture'
        req=urllib.request.Request(f'http://127.0.0.1:{port}/index.html',headers={'Range':'bytes=1-3'})
        with urllib.request.urlopen(req) as response:
            assert response.status==206
            assert response.headers['Content-Range']=='bytes 1-3/6'
            assert response.read()==b'ubl'
        print('PASS: public index; sibling-prefix, encoded traversal, symlink directory/file rejected')
    finally: proc.terminate(); proc.wait()
