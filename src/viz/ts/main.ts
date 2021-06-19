import $ from 'jquery';
import { MainDocument, DragDropJson } from './app';
import { ProofTrace } from './proof-trace';
import { ProofInteraction } from './proof-interaction';
import { BenchmarksDB } from './benchmarks';



declare var nw: any;

if (typeof nw !== 'undefined') {
    var win = nw.Window.get();
    //win.zoomLevel = -2;
    Object.assign(window, {
        printDocument() {
            win.print({autoprint: false, scaleFactor: 5});
        }
    });
}


$(async () => {
    var doc = new MainDocument($('#proof-trace-pane'), $('#notifications'));
    doc.on('open', pt => Object.assign(window, {pt}));

    document.querySelector('#document-area').replaceWith(doc.$el);

    const bench = await BenchmarksDB.load();
    doc.setBenchmarks(bench.data);

    async function startBenchmark(w: {dir: string, fn: string}) {
        var spec = bench.getSpec(w.dir, w.fn);
        doc.hideBenchmarks();
        doc.new();
        doc.setEditorText([...spec.defs, spec.in].join('\n'));
        await doc.pi.start(spec);
        Object.assign(window, {spec});
    }

    doc.on('benchmarks:action', startBenchmark);

    /*
    try {
        await doc.openRecent({silent: true});
    }
    catch (e) { console.error('open failed:', e); }
    */
    doc.new();

    var drop = new DragDropJson($('html'));
    drop.on('open', async ({file}) => {
        try {
            await doc.open(file);
        }
        catch (e) { console.error('open failed:', e); }
    });

    /* Start a benchmark on load if instructed so by local config */
    var openOnStart = localStorage['openOnStart']
    if (openOnStart) {
        startBenchmark(JSON.parse(openOnStart));
    }

    Object.assign(window, {doc, bench});
});