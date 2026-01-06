// Workers.FFI.SqlStorage

// クエリ実行
export const exec = (storage) => (sql) => {
  return storage.exec(sql);
};

export const _execWithParams = (storage) => (sql) => (params) => {
  return storage.exec(sql, ...params);
};

// 結果取得
export const _one = (cursor) => {
  const result = cursor.one();
  return result === undefined ? null : result;
};

export const toArray = (cursor) => {
  return cursor.toArray();
};

export const raw = (cursor) => {
  return cursor.raw({ columnNames: false }).toArray();
};

// メタデータ
export const columnNames = (cursor) => {
  return cursor.columnNames;
};

export const rowsRead = (cursor) => {
  return cursor.rowsRead;
};

export const rowsWritten = (cursor) => {
  return cursor.rowsWritten;
};
