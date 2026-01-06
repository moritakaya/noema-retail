// Adapter.StripeAdapter FFI

export const getCurrentTime = (onError, onSuccess) => {
  onSuccess(Date.now());
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const parseFloat = (str) => Number.parseFloat(str);

export const floor = (n) => Math.floor(n);

export const abs = (n) => Math.abs(n);

export const take = (n) => (str) => str.slice(0, n);

export const drop = (n) => (str) => str.slice(n);

export const any = (pred) => (arr) => arr.some(pred);
