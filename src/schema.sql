CREATE TABLE function_context_property (
    instance BLOB PRIMARY KEY,
    property BLOB
);

CREATE TABLE preemption_count_annotation (
    stable_crate_id INTEGER,
    local_def_id INTEGER,
    adjustment INTEGER,
    assumption_lo INTEGER,
    assumption_hi INTEGER
);
