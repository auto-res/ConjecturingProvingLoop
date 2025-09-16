import subprocess
import json
import concurrent.futures
from loguru import logger

class LeanClient:
    def __init__(self, workdir='../mathlib4'):
        self.workdir = workdir
        self.proc = None
        self._start_process()
    
    def _start_process(self):
        """Leanプロセスを開始"""
        self.proc = subprocess.Popen(
            ['stdbuf', '-oL', '-eL', '/root/.elan/bin/lake', 'env', '../repl/.lake/build/bin/repl'],
            cwd=self.workdir,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            encoding="utf-8",
            text=True,
            bufsize=1,
        )
    
    def send_reql(self, s: str, context: str, env=None, timeout=100.):
        """Leanにリクエストを送信"""
        req = {"cmd": s}
        
        if env is not None:
            req.update({"env": env})
        
        assert self.proc.poll() is None
        self.proc.stdin.write(json.dumps(req) + "\n\n")
        self.proc.stdin.flush()
        output = ""
        
        while True:
            if self.proc.poll() is not None:
                logger.error(f"Lean process has terminated: input: {s}, output: {output}")
                raise Exception("Lean process has terminated")
            
            try:
                with concurrent.futures.ThreadPoolExecutor() as executor:
                    future = executor.submit(self.proc.stdout.readline)
                    output += future.result(timeout=timeout)
            except concurrent.futures.TimeoutError:
                logger.error(f"Timeout waiting for response to command: {s}")
                raise Exception("Timeout waiting for response to command")
            
            try:
                data = json.loads(output)
                logger.info(data)
                return data
            except json.JSONDecodeError:
                continue
    
    def close(self):
        """プロセスを終了"""
        if self.proc and self.proc.poll() is None:
            self.proc.terminate()
            self.proc.wait()

# グローバルインスタンス（必要に応じて）
_lean_client = None

def get_lean_client():
    """グローバルLeanClientインスタンスを取得"""
    global _lean_client
    if _lean_client is None:
        _lean_client = LeanClient()
    return _lean_client

def close_lean_client():
    """グローバルLeanClientインスタンスを終了"""
    global _lean_client
    if _lean_client:
        _lean_client.close()
        _lean_client = None 