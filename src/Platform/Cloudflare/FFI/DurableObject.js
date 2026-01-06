// Workers.FFI.DurableObject

// State 操作
export const getStorage = (state) => state.storage;

export const _getId = (state) => state.id;

export const _waitUntil = (state) => (promise) => () => {
  state.waitUntil(new Promise((resolve) => {
    promise();
    resolve();
  }));
};

// Namespace 操作
export const _idFromName = (namespace) => (name) => () => {
  return namespace.idFromName(name);
};

export const _idFromString = (namespace) => (str) => () => {
  try {
    return namespace.idFromString(str);
  } catch {
    return null;
  }
};

export const _newUniqueId = (namespace) => () => {
  return namespace.newUniqueId();
};

export const _get = (namespace) => (id) => () => {
  return namespace.get(id);
};

// Stub 操作
export const _fetch = (stub) => (request) => (onError, onSuccess) => {
  stub.fetch(request)
    .then(onSuccess)
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

// Storage 操作（Key-Value）
export const _storageGet = (storage) => (key) => (onError, onSuccess) => {
  storage.get(key)
    .then((value) => onSuccess(value === undefined ? null : value))
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const _storagePut = (storage) => (key) => (value) => (onError, onSuccess) => {
  storage.put(key, value)
    .then(() => onSuccess())
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const _storageDelete = (storage) => (key) => (onError, onSuccess) => {
  storage.delete(key)
    .then((deleted) => onSuccess(deleted))
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const _storageList = (storage) => (onError, onSuccess) => {
  storage.list()
    .then((map) => onSuccess(Array.from(map.keys())))
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const _storageTransaction = (storage) => (callback) => (onError, onSuccess) => {
  storage.transaction(async (txn) => {
    return new Promise((resolve, reject) => {
      callback(txn)(reject, resolve);
    });
  })
    .then(onSuccess)
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

// Alarm 操作
export const _setAlarm = (storage) => (time) => (onError, onSuccess) => {
  storage.setAlarm(time)
    .then(() => onSuccess())
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const _getAlarm = (storage) => (onError, onSuccess) => {
  storage.getAlarm()
    .then((alarm) => onSuccess(alarm === null ? null : alarm.getTime()))
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const _deleteAlarm = (storage) => (onError, onSuccess) => {
  storage.deleteAlarm()
    .then(() => onSuccess())
    .catch(onError);
  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

// SQL Storage
export const getSql = (storage) => storage.sql;
