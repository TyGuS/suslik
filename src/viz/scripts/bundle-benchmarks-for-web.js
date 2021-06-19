#!/usr/bin/env node

import fs from 'fs';
import path from 'path';
import find from 'find';

const BENCHMARKS_ROOT = 'src/test/resources/synthesis/all-benchmarks';

function main() {
    var dir = BENCHMARKS_ROOT,
        collection = {};

    function bucket(k) {
        var v = collection[k];
        if (!v) v = collection[k] = {};
        return v;
    }

    find.eachfile(/\.(syn|def)$/, dir, fn => {
        var rel = path.relative(dir, fn),
            reldir = path.dirname(rel), base = path.basename(rel);
        console.log(reldir, base);
        bucket(reldir)[base] = fs.readFileSync(fn, 'utf-8');
    }).end(() => {
        fs.writeFileSync('dist/benchmarks.db.json', JSON.stringify(collection));
    });
}

main();