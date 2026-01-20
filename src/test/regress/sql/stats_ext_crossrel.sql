-- Join MCV statistics tests
--
-- Note: tables for which we check estimated row counts should be created
-- with autovacuum_enabled = off, so that we don't have unstable results
-- from auto-analyze happening when we didn't expect it.
--

--
-- Test CREATE STATISTICS syntax for join MCV statistics.
--

CREATE TABLE keywords2 (
    id INTEGER PRIMARY KEY,
    keyword TEXT NOT NULL,
    phonetic_code character varying(5)
);

CREATE TABLE movie_keywords2 (
    movie_id INTEGER PRIMARY KEY,
    keyword_id INTEGER NOT NULL  -- No FOREIGN KEY reference
);

-- Insert tightly correlated data into the "referenced" table
INSERT INTO keywords2 (id, keyword, phonetic_code)
SELECT
    i,
    'keyword_' || i,
    'ph_' || i
FROM generate_series(1, 50) i;

-- Insert data into the "referencing" table with skewed distribution
INSERT INTO movie_keywords2 (movie_id, keyword_id)
SELECT
    i,
    CASE
        WHEN i % 100 < 60 THEN (i % 10) + 1      -- 60% keyword_ids 1-10 (6% frequency per keyword)
        WHEN i % 100 < 90 THEN (i % 10) + 11     -- 30% keyword_ids 11-20 (3% frequency per keyword)
        ELSE (i % 10) + 21                       -- 10% keyword_ids 21-30 (1% frequency per keyword)
    END
FROM generate_series(1, 10000) i;

ANALYZE keywords2;
ANALYZE movie_keywords2;

-- Create join MCV statistics on a single filter column (keyword)
CREATE STATISTICS movie_keywords2_keyword_stats (mcv)
ON k.keyword
FROM movie_keywords2 mk JOIN keywords2 k ON (mk.keyword_id = k.id);
ANALYZE movie_keywords2;

-- Show the stats in catalog
SELECT s.stxname,
       s.stxrelid::regclass,
       s.stxotherrel::regclass,
       s.stxjoinkeys,
       s.stxkeys,
       s.stxkind,
       s.stxstattarget,
       s.stxexprs
FROM pg_statistic_ext s
WHERE s.stxname = 'movie_keywords2_keyword_stats';

-- FIXME: this is incorrect.
-- Need to implement pg_get_statisticsobjdef for join MCV statistics
SELECT pg_get_statisticsobjdef(oid) FROM pg_statistic_ext WHERE stxname = 'movie_keywords2_keyword_stats';

SELECT m.index,
       m.values,
       m.nulls,
       ROUND(m.frequency::numeric, 2) AS frequency
FROM pg_statistic_ext s
JOIN pg_statistic_ext_data d ON (s.oid = d.stxoid)
CROSS JOIN LATERAL pg_join_mcv_list_items(d.stxdjoinmcv) AS m
WHERE s.stxname = 'movie_keywords2_keyword_stats'
ORDER BY m.index;

-- Create join MCV statistics on multiple filter columns (keyword + phonetic_code)
CREATE STATISTICS movie_keywords2_multi_stats (mcv)
ON k.keyword, k.phonetic_code
FROM movie_keywords2 mk JOIN keywords2 k ON (mk.keyword_id = k.id);
ANALYZE movie_keywords2;

-- Show the stats in catalog
SELECT s.stxname,
       s.stxrelid::regclass,
       s.stxotherrel::regclass,
       s.stxjoinkeys,
       s.stxkeys,
       s.stxkind,
       s.stxstattarget,
       s.stxexprs
FROM pg_statistic_ext s
WHERE s.stxname = 'movie_keywords2_multi_stats';

SELECT m.index,
       m.values,
       m.nulls,
       ROUND(m.frequency::numeric, 2) AS frequency
FROM pg_statistic_ext s
JOIN pg_statistic_ext_data d ON (s.oid = d.stxoid)
CROSS JOIN LATERAL pg_join_mcv_list_items(d.stxdjoinmcv) AS m
WHERE s.stxname = 'movie_keywords2_multi_stats'
ORDER BY m.index;

-- Verify the join MCV statistics are used for single equality predicates
-- on the filter column of the referenced table
SELECT * FROM check_estimated_rows('
    SELECT * FROM movie_keywords2 mk, keywords2 k
    WHERE k.keyword = ''keyword_1'' AND k.id = mk.keyword_id
');

SELECT * FROM check_estimated_rows('
    SELECT * FROM movie_keywords2 mk, keywords2 k
    WHERE k.keyword = ''keyword_15'' AND k.id = mk.keyword_id
');

SELECT * FROM check_estimated_rows('
    SELECT * FROM movie_keywords2 mk, keywords2 k
    WHERE k.keyword = ''keyword_25'' AND k.id = mk.keyword_id
');

SELECT * FROM check_estimated_rows('
    SELECT * FROM movie_keywords2 mk, keywords2 k
    WHERE k.phonetic_code = ''ph_1'' AND k.id = mk.keyword_id
');

SELECT * FROM check_estimated_rows('
    SELECT * FROM movie_keywords2 mk, keywords2 k
    WHERE k.phonetic_code = ''ph_15'' AND k.id = mk.keyword_id
');

SELECT * FROM check_estimated_rows('
    SELECT * FROM movie_keywords2 mk, keywords2 k
    WHERE k.phonetic_code = ''ph_25'' AND k.id = mk.keyword_id
');

-- Ensure the join MCV statistics are used for IN predicates
-- on the filter column of the referenced table
SELECT * FROM check_estimated_rows('
    SELECT * FROM movie_keywords2 mk, keywords2 k
    WHERE k.keyword IN (''keyword_1'', ''keyword_2'', ''keyword_3'')
      AND k.id = mk.keyword_id
');

-- Ensure the join MCV statistics are used for equality predicates
-- on multiple filter columns of the referenced table
SELECT * FROM check_estimated_rows('
    SELECT * FROM movie_keywords2 mk, keywords2 k
    WHERE k.keyword = ''keyword_1''
      AND k.phonetic_code = ''ph_1''
      AND k.id = mk.keyword_id
');

-- Zero join MCV match, falls back to standard estimation: 10000 * 1 / 50 = 200.
SELECT * FROM check_estimated_rows('
    SELECT * FROM movie_keywords2 mk, keywords2 k
    WHERE k.keyword = ''keyword_1''
      AND k.phonetic_code = ''ph_15''
      AND k.id = mk.keyword_id
');

-- Verify syntax error cases
CREATE STATISTICS bad_stats1 (mcv) ON k.keyword;
CREATE STATISTICS bad_stats2 (mcv) ON k.keyword FROM movie_keywords2 mk, keywords2 k;
CREATE STATISTICS bad_stats3 (mcv) FROM movie_keywords2 mk JOIN keywords2 k ON (mk.keyword_id = k.id);
CREATE STATISTICS bad_stats4 (mcv) ON keyword FROM movie_keywords2 mk JOIN keywords2 k ON (mk.keyword_id = k.id);
CREATE STATISTICS bad_stats5 (mcv) ON lower(k.keyword) FROM movie_keywords2 mk JOIN keywords2 k ON (mk.keyword_id = k.id);
CREATE STATISTICS bad_stats6 (mcv) ON k.keyword FROM (movie_keywords2 mk JOIN keywords2 k ON (mk.keyword_id = k.id)) JOIN keywords2 k2 ON (k.id = k2.id);

-- Cleanup
DROP TABLE movie_keywords2 CASCADE;
DROP TABLE keywords2 CASCADE;
