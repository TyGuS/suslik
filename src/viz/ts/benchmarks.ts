

class BenchmarksDB {
    db: BenchmarksDB.Data

    constructor(db: BenchmarksDB.Data) {
        this.db = db;
    }

    getSpec(dir: string, fn: string) {
        return {
            name: `${dir}:${fn}`, 
            defs: this.getDefs(dir),
            in: this.getInputSpec(dir, fn)
        };
    }

    getDefs(dir: string) {
        return Object.entries(this.db[dir])
            .map(([fn, txt]) => fn.endsWith('.def') && txt).filter(x => x);
    }

    getInputSpec(dir: string, fn: string) {
        return this.db[dir][fn].match(/###([^]*?)###/)[1];
    }

    static async load(url = '/benchmarks.db.json') {
        return new BenchmarksDB(await (await fetch(url)).json());
    }
}

namespace BenchmarksDB {
    export type Data = {[dir: string]: {[fn: string]: string}};
}


export { BenchmarksDB }
