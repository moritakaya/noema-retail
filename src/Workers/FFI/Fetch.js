// Workers.FFI.Fetch

export const _fetch = (url) => (onError, onSuccess) => {
  fetch(url)
    .then(onSuccess)
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const _fetchWithInit = (url) => (init) => (onError, onSuccess) => {
  const requestInit = {
    method: init.method,
    headers: init.headers,
  };
  if (init.body !== null) {
    requestInit.body = init.body;
  }
  fetch(url, requestInit)
    .then(onSuccess)
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};
