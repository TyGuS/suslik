#!/usr/bin/env node

import fs from 'fs';
import path from 'path';
import find from 'find';

const BENCHMARKS_ROOT = 'src/test/resources/synthesis/all-benchmarks',
      TUTORIAL_ROOT = 'ext/tutorial';

function main() {
    var physical = TUTORIAL_ROOT, logical = '.',
        collection = {};

    function bucket(k) {
        var v = collection[k];
        if (!v) v = collection[k] = {};
        return v;
    }

    find.eachfile(/\.(sus|syn|def)$/, physical, fn => {
        var rel = path.join(logical, path.relative(physical, fn)),
            reldir = path.dirname(rel), base = path.basename(rel);
        console.log(reldir, '/', base);
        bucket(reldir)[base] = fs.readFileSync(fn, 'utf-8');
    }).end(() => {
        fs.writeFileSync('dist/benchmarks.db.json', JSON.stringify(collection));
    });
}

main();