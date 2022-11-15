CREATE TABLE mir (
    stable_crate_id INTEGER,
    local_def_id INTEGER,
    mir BLOB,
    PRIMARY KEY (stable_crate_id, local_def_id)
);