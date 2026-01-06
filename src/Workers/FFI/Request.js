// Workers.FFI.Request

export const url = (request) => request.url;

export const _method = (request) => request.method;

export const _getHeader = (request) => (name) => () => {
  return request.headers.get(name);
};

export const headers = (request) => () => {
  const result = {};
  for (const [key, value] of request.headers.entries()) {
    result[key] = value;
  }
  return result;
};

export const _text = (request) => (onError, onSuccess) => {
  request.text()
    .then(onSuccess)
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const _json = (request) => (onError, onSuccess) => {
  request.json()
    .then(onSuccess)
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const _newRequest = (url) => () => {
  return new Request(url);
};

export const _newRequestWithInit = (url) => (init) => () => {
  const requestInit = {
    method: init.method,
    headers: init.headers,
  };
  if (init.body !== null) {
    requestInit.body = init.body;
  }
  return new Request(url, requestInit);
};

export const clone = (request) => () => {
  return request.clone();
};
