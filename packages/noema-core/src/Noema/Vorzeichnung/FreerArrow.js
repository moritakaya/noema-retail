// FFI for Noema.Vorzeichnung.FreerArrow
// Existential type encoding

export const mkExists = function(fa) {
  return fa;
};

export const runExists = function(f) {
  return function(ex) {
    return f(ex);
  };
};

export const unsafeCoerce = function(x) {
  return x;
};
