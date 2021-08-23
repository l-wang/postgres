CREATE EXTENSION IF NOT EXISTS blackhole_am;
CREATE TABLE blackhole_tab (a int) USING blackhole_am;
SELECT * FROM blackhole_tab;
INSERT INTO blackhole_tab VALUES (42);
SELECT * FROM blackhole_tab;
INSERT INTO blackhole_tab VALUES (1), (23);
SELECT * FROM blackhole_tab;
