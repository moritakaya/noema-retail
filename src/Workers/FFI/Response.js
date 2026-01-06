// Workers.FFI.Response

export const status = (response) => response.status;

export const statusText = (response) => response.statusText;

export const ok = (response) => response.ok;

export const _headers = (response) => () => {
  const result = {};
  for (const [key, value] of response.headers.entries()) {
    result[key] = value;
  }
  return result;
};

export const _text = (response) => (onError, onSuccess) => {
  response.text()
    .then(onSuccess)
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const _json = (response) => (onError, onSuccess) => {
  response.json()
    .then(onSuccess)
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const _newResponse = (body) => () => {
  return new Response(body);
};

export const _newResponseWithInit = (body) => (init) => () => {
  return new Response(body, {
    status: init.status,
    statusText: init.statusText,
    headers: init.headers,
  });
};

export const _jsonResponse = (data) => () => {
  return new Response(JSON.stringify(data), {
    status: 200,
    headers: {
      'Content-Type': 'application/json',
    },
  });
};

export const _redirectResponse = (location) => (statusCode) => () => {
  return Response.redirect(location, statusCode);
};
