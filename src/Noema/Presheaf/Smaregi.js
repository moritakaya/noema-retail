// Adapter.SmaregiAdapter FFI

export const currentTimestamp' = (onError, onSuccess) => {
  onSuccess(Date.now());
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};
