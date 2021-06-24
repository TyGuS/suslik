import $ from 'jquery';
import { SuSLikApp, MainDocument, DragDropJson } from './app';
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
    var app = new SuSLikApp($('#notifications'));

    document.querySelector('#document-area').replaceWith(app.$el);

    const bench = await BenchmarksDB.load();
    app.setBenchmarks(bench.data);

    async function startBenchmark(w: {dir: string, fn: string}) {
        var spec = bench.getSpec(w.dir, w.fn),
            doc = new MainDocument('benchmark-0', app.app.$refs.proofTrace as any)
        app.hideBenchmarks();
        app.setEditorText(BenchmarksDB.Data.unparseSpec(spec));
        app.add(doc);
        doc.new();
        await doc.pi.start(spec);
    }

    async function restartBenchmark(mode?: ProofInteraction.Data.ProofMode) {
        console.log(app.getEditorText());
        var spec = BenchmarksDB.Data.parseSpec('todo', app.getEditorText()),
            doc = new MainDocument('benchmark-0', app.app.$refs.proofTrace as any);
        app.add(doc);
        doc.new();
        await doc.pi.start(spec, mode);
    }

    function proofMode() {
        return app.options.auto ? ProofInteraction.Data.ProofMode.AUTOMATIC
                                : ProofInteraction.Data.ProofMode.INTERACTIVE;
    }

    app.on('benchmarks:action', startBenchmark);
    app.on('proofTrace:action', (action) => {
        switch (action.type) {
            case 'restart': restartBenchmark(proofMode()); break;
        }
    });

    /*
    try {
        await doc.openRecent({silent: true});
    }
    catch (e) { console.error('open failed:', e); }
    */

    var drop = new DragDropJson($('html'));
    drop.on('open', async ({file}) => {
        try {
            var doc = new MainDocument('json-0', app.app.$refs.proofTrace as any)
            await doc.open(file);
            app.add(doc);
        }
        catch (e) { console.error('open failed:', e); }
    });

    /* Start a benchmark on load if instructed so by local config */
    var openOnStart = localStorage['openOnStart']
    if (openOnStart) {
        startBenchmark(JSON.parse(openOnStart));
    }

    Object.assign(window, {app, bench});
});