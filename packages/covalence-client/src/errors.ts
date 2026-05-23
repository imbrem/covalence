export class CovalenceError extends Error {
  readonly status: number;
  readonly notFound: boolean;

  constructor(status: number, message: string) {
    super(message);
    this.name = 'CovalenceError';
    this.status = status;
    this.notFound = status === 404;
  }
}
