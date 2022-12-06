CREATE TABLE function_context_property (
    instance BLOB PRIMARY KEY,
    property BLOB
);

CREATE TABLE preemption_count_annotation (
    local_def_id INTEGER PRIMARY KEY,
    adjustment INTEGER,
    expectation_lo INTEGER,
    expectation_hi INTEGER
);
