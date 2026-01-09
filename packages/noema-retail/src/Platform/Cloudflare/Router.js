// Platform.Cloudflare.Router FFI

export const parseUrlPath = (urlString) => {
  try {
    const url = new URL(urlString);
    return url.pathname.split('/').filter(s => s.length > 0);
  } catch (e) {
    // Relative path
    return urlString.split('/').filter(s => s.length > 0);
  }
};

export const startsWith = (prefix) => (str) => str.startsWith(prefix);

export const drop = (n) => (str) => str.slice(n);

export const length = (arr) => arr.length;
