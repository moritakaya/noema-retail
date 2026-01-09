// Workers.Attractor.SubjectAttractor FFI

export const parseUrlPath = (urlString) => {
  try {
    const url = new URL(urlString);
    return url.pathname.split('/').filter(s => s.length > 0);
  } catch {
    // 相対パスの場合
    return urlString.split('/').filter(s => s.length > 0);
  }
};
