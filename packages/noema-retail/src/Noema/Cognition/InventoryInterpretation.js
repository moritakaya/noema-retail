// Noema.Cognition.InventoryInterpretation FFI

// SqlStorage functions (Cloudflare Durable Objects SQLite API)
export const exec = (sql) => (query) => {
  return sql.exec(query);
};

export const execWithParams = (sql) => (query) => (params) => {
  return sql.exec(query, ...params);
};

export const one = (cursor) => {
  const rows = cursor.toArray();
  if (rows.length === 0) {
    return null; // Maybe.Nothing
  }
  return rows[0]; // Maybe.Just
};

export const toArray = (cursor) => {
  return cursor.toArray();
};

export const getField = (obj) => (field) => {
  return obj[field];
};

export const generateId = () => {
  return crypto.randomUUID();
};
