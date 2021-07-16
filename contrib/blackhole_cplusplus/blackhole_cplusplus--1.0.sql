/* blackhole_cplusplus/blackhole_plusplus--1.0.sql */

-- complain if script is sourced in psql, rather than via CREATE EXTENSION
\echo Use "CREATE EXTENSION blackhole_cplusplus" to load this file. \quit

-- This is a blackhole C++ function.
CREATE FUNCTION blackhole_cplusplus()
RETURNS text
AS 'MODULE_PATHNAME'
LANGUAGE C;

CREATE FUNCTION blackhole_am_handler(internal)
    RETURNS table_am_handler
AS 'MODULE_PATHNAME'
    LANGUAGE C;

-- Access method
CREATE ACCESS METHOD blackhole_am TYPE TABLE HANDLER blackhole_am_handler;
COMMENT ON ACCESS METHOD blackhole_am IS 'template table AM eating all data';
