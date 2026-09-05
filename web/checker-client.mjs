// One bounded job at a time; queued work is replaced by its newest channel request.
export class CheckerClient {
  constructor({ createWorker, timeoutMs = 10000, onBusy = () => {} } = {}) {
    this.createWorker = createWorker ?? (() => new Worker(new URL('./checker-worker.js?v=2', import.meta.url), {type: 'module'}));
    this.timeoutMs = timeoutMs;
    this.onBusy = onBusy;
    this.queue = [];
    this.active = null;
    this.worker = null;
    this.serial = 0;
  }

  run(method, args, channel = method) {
    return new Promise((resolve, reject) => {
      this.queue = this.queue.filter(job => {
        if (job.channel !== channel) return true;
        job.resolve(null);
        return false;
      });
      this.queue.push({ id: ++this.serial, method, args, channel, resolve, reject });
      this.pump();
    });
  }

  pump() {
    if (this.active || !this.queue.length) return;
    const job = this.queue.shift();
    this.active = job;
    this.onBusy(true);
    try {
      if (!this.worker) {
        const worker = this.createWorker();
        this.worker = worker;
        worker.onmessage = ({ data }) => {
          if (worker !== this.worker || data.id !== this.active?.id) return;
          if (data.error) {
            this.stop(new Error(data.error));
            return;
          }
          const completed = this.active;
          clearTimeout(this.timer);
          this.active = null;
          completed.resolve(data.result);
          this.onBusy(this.queue.length > 0);
          this.pump();
        };
        worker.onerror = event => {
          event.preventDefault?.();
          if (worker === this.worker) this.stop(new Error('The checker stopped unexpectedly. Your source is preserved; press Check to retry. If it fails again, download your source or project before reloading the page.'));
        };
      }
      this.timer = setTimeout(() => this.stop(new Error('Checking took too long and was stopped. Your source is preserved; simplify the proof or press Check to retry.')), this.timeoutMs);
      this.worker.postMessage({ id: job.id, method: job.method, args: job.args });
    } catch (error) {
      this.stop(error);
    }
  }

  stop(error = null) {
    clearTimeout(this.timer);
    this.worker?.terminate();
    this.worker = null;
    const jobs = [...(this.active ? [this.active] : []), ...this.queue];
    this.active = null;
    this.queue = [];
    for (const job of jobs) error ? job.reject(error) : job.resolve(null);
    this.onBusy(false);
  }
}
