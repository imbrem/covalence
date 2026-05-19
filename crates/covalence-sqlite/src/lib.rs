pub use rusqlite::{self, Connection, Error, params};

use std::path::Path;

/// Open a SQLite connection at the given path with recommended settings:
/// WAL mode, NORMAL sync, 5 second busy timeout.
pub fn open(path: impl AsRef<Path>) -> Result<Connection, Error> {
    let conn = Connection::open(path)?;
    configure(&conn)?;
    Ok(conn)
}

/// Open an in-memory SQLite connection with the same pragmas.
pub fn open_memory() -> Result<Connection, Error> {
    let conn = Connection::open_in_memory()?;
    configure(&conn)?;
    Ok(conn)
}

fn configure(conn: &Connection) -> Result<(), Error> {
    conn.pragma_update(None, "journal_mode", "WAL")?;
    conn.pragma_update(None, "synchronous", "NORMAL")?;
    conn.busy_timeout(std::time::Duration::from_secs(5))?;
    Ok(())
}
