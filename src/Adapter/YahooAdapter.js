// Adapter.YahooAdapter FFI

export const getCurrentTime = (onError, onSuccess) => {
  onSuccess(Date.now());
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};
