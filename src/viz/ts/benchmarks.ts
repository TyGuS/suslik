

class BenchmarksDB {
    data: BenchmarksDB.Data

    constructor(data: BenchmarksDB.Data) {
        this.data = data;
    }

    getSpec(dir: string, fn: string) {
        return {
            name: `${dir}:${fn}`, 
            defs: this.getDefs(dir),
            in: this.getInputSpec(dir, fn)
        };
    }

    getDefs(dir: string) {
        return Object.entries(this.data[dir])
            .map(([fn, txt]) => fn.endsWith('.def') && txt).filter(x => x);
    }

    getInputSpec(dir: string, fn: string) {
        return this.data[dir][fn].match(/###+([^]*?)###+/)[1];
    }

    static async load(url = '/benchmarks.db.json') {
        return new BenchmarksDB(await (await fetch(url)).json());
    }
}

namespace BenchmarksDB {
    export type Data = {[dir: string]: {[fn: string]: string}};
}


export { BenchmarksDB }
