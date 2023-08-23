import threading
import time
import os

throttle = threading.Semaphore(4)

def commands():
    for type in ['series']:
        for stages in range(3):
            for iteration in range(10):
                yield f'/home/kbaldor/thorium/thorium/thorium-verify.py compose-{type}-{stages+1}.Th -r Pipeline -p bounded -n 3 > compose-perf/compose-{type}-{stages+1}-{iteration+1}'

def worker(command):
    global throttle
    print(command)
    os.system(command)
    throttle.release()

for command in commands():
    throttle.acquire()
    threading.Thread(target=worker,args=(command,)).start()
