// Noema.Handler.InventoryHandler FFI

export const generateId = () => {
  return crypto.randomUUID();
};

export const getField = (obj) => (field) => {
  return obj[field];
};
