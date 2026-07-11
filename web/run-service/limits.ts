// Per-IP token bucket + a bounded concurrency gate. Both are COST controls
// (public-abuse surface = resource exhaustion, interactive-tour-design.md §3);
// the jail is the safety boundary, these keep one client from starving others.

export class TokenBucket {
  private buckets = new Map<string, { tokens: number; last: number }>();

  constructor(
    private capacity: number,
    private refillPerSec: number,
  ) {}

  // true = allowed (a token was spent); false = throttled.
  take(key: string, now = Date.now()): boolean {
    let b = this.buckets.get(key);
    if (b === undefined) {
      b = { tokens: this.capacity, last: now };
      this.buckets.set(key, b);
    }
    const elapsed = (now - b.last) / 1000;
    b.tokens = Math.min(this.capacity, b.tokens + elapsed * this.refillPerSec);
    b.last = now;
    if (b.tokens < 1) return false;
    b.tokens -= 1;
    return true;
  }

  // Drop buckets that have fully refilled (bounded memory under many IPs).
  sweep(now = Date.now()): void {
    for (const [key, b] of this.buckets) {
      const elapsed = (now - b.last) / 1000;
      if (b.tokens + elapsed * this.refillPerSec >= this.capacity) {
        this.buckets.delete(key);
      }
    }
  }
}

// A counting semaphore with a bounded wait-queue. acquire() rejects immediately
// when the queue is full (→ 503) rather than growing unboundedly.
export class ConcurrencyGate {
  private inFlight = 0;
  private queue: Array<() => void> = [];

  constructor(
    private maxConcurrent: number,
    private maxQueue: number,
  ) {}

  async acquire(): Promise<() => void> {
    if (this.inFlight < this.maxConcurrent) {
      this.inFlight++;
      return () => this.release();
    }
    if (this.queue.length >= this.maxQueue) {
      throw new QueueFullError();
    }
    await new Promise<void>((resolve) => this.queue.push(resolve));
    this.inFlight++;
    return () => this.release();
  }

  private release(): void {
    this.inFlight--;
    const next = this.queue.shift();
    if (next) next();
  }
}

export class QueueFullError extends Error {
  constructor() {
    super("run queue full");
    this.name = "QueueFullError";
  }
}
