import $ from 'jquery';
import Vue from 'vue';
import { SuSLikApp, MainDocument, DragDropJson } from './app';
import { ProofInteraction } from './proof-interaction';
import { BenchmarksDB } from './benchmarks';

import ProofMode = ProofInteraction.Data.ProofMode;



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

    async function startBenchmark(w: {dir: string, fn: string}, mode: ProofMode = ProofMode.INTERACTIVE) {
        var spec = bench.getSpec(w.dir, w.fn),
            doc = new MainDocument(`benchmark-0-${mode}`, app.panes.proofTrace,
                                   OPTIONS[mode]);
        app.hideBenchmarks();
        app.clear();
        app.setEditorText(BenchmarksDB.Data.unparseSpec(spec));
        app.add(doc);
        doc.new();
        await doc.pi.start(spec, mode);
    }

    /** @todo Pretty hideous duplication do refactor please */
    async function restartBenchmark(mode: ProofMode = ProofMode.INTERACTIVE) {
        var spec = BenchmarksDB.Data.parseSpec('todo', app.getEditorText()),
            doc = new MainDocument(`benchmark-0-${mode}`, app.panes.proofTrace,
                                   OPTIONS[mode]);
        app.add(doc);
        doc.new();
        await doc.pi.start(spec, mode);
    }

    async function switchMode(mode: ProofMode) {
        var docId = `benchmark-0-${mode}`;
        if (app.has(docId))
            app.switchTo(docId);
        else
            restartBenchmark(mode);
    }

    function proofMode() {
        return app.options.auto ? ProofMode.AUTOMATIC : ProofMode.INTERACTIVE;
    }

    app.view.$watch(proofMode, switchMode);  /* neat ;) */

    const OPTIONS: {[mode: string]: MainDocument.Options} = {
        [ProofMode.AUTOMATIC]: {throttle: 750},
        [ProofMode.INTERACTIVE]: {expandImmediately: true}
    };

    app.on('benchmarks:action', w => startBenchmark(w, proofMode()));
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
            var doc = new MainDocument('json-0', app.panes.proofTrace)
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