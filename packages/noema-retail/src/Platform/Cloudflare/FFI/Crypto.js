// Workers.FFI.Crypto

export const _hmacSha256 = (message) => (secret) => (onError, onSuccess) => {
  (async () => {
    try {
      const encoder = new TextEncoder();
      const keyData = encoder.encode(secret);
      const messageData = encoder.encode(message);

      const key = await crypto.subtle.importKey(
        'raw',
        keyData,
        { name: 'HMAC', hash: 'SHA-256' },
        false,
        ['sign']
      );

      const signature = await crypto.subtle.sign('HMAC', key, messageData);
      const hashArray = Array.from(new Uint8Array(signature));
      const hashHex = hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
      onSuccess(hashHex);
    } catch (error) {
      onError(error);
    }
  })();

  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const _sha256 = (message) => (onError, onSuccess) => {
  (async () => {
    try {
      const encoder = new TextEncoder();
      const data = encoder.encode(message);
      const hashBuffer = await crypto.subtle.digest('SHA-256', data);
      const hashArray = Array.from(new Uint8Array(hashBuffer));
      const hashHex = hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
      onSuccess(hashHex);
    } catch (error) {
      onError(error);
    }
  })();

  return (cancelError, onCancelError, onCancelSuccess) => {
    onCancelSuccess();
  };
};

export const randomUUID = () => crypto.randomUUID();

export const _randomBytes = (length) => () => {
  const bytes = new Uint8Array(length);
  crypto.getRandomValues(bytes);
  return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
};

export const base64Encode = (str) => {
  const encoder = new TextEncoder();
  const data = encoder.encode(str);
  return btoa(String.fromCharCode.apply(null, data));
};

export const base64Decode = (str) => {
  const decoded = atob(str);
  return decoded;
};

export const hexEncode = (str) => {
  const encoder = new TextEncoder();
  const data = encoder.encode(str);
  return Array.from(data).map(b => b.toString(16).padStart(2, '0')).join('');
};

export const secureCompare = (a) => (b) => {
  if (a.length !== b.length) {
    // 長さが異なる場合も一定時間で比較
    let result = a.length ^ b.length;
    for (let i = 0; i < Math.max(a.length, b.length); i++) {
      const charA = a.charCodeAt(i % a.length) || 0;
      const charB = b.charCodeAt(i % b.length) || 0;
      result |= charA ^ charB;
    }
    return result === 0;
  }

  let result = 0;
  for (let i = 0; i < a.length; i++) {
    result |= a.charCodeAt(i) ^ b.charCodeAt(i);
  }
  return result === 0;
};
