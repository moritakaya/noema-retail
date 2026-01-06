// Main FFI

export const parseUrlPath = (urlString) => {
  try {
    const url = new URL(urlString);
    return url.pathname.split('/').filter(s => s.length > 0);
  } catch {
    return urlString.split('/').filter(s => s.length > 0);
  }
};

export const getInventoryNamespace = (env) => env.INVENTORY_ATTRACTOR;

export const createInternalRequest = (pathParts) => (originalRequest) => () => {
  const internalUrl = 'http://internal/' + pathParts.join('/');
  return new Request(internalUrl, {
    method: originalRequest.method,
    headers: originalRequest.headers,
    body: originalRequest.body,
  });
};

export const _createDOClass = (handlers) => () => {
  // Note: This is a factory that will be used by the runtime wrapper
  return {
    create: handlers.create,
    fetch: handlers.fetch,
    alarm: handlers.alarm,
  };
};
