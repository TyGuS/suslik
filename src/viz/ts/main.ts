import $ from 'jquery';
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
    if (window.location.search !== '?cheater!')
        delete bench.data['solutions'];  // :P

    const DEFAULT_SCRATCH = {dir: 'scratchpath', fn: 'untitled-0.sus'}
    bench.data[DEFAULT_SCRATCH.dir] = {
        [DEFAULT_SCRATCH.fn]: '// write your own stuff here'
    };

    app.setBenchmarks(bench.data);

    var activeBenchmark: {name: string, spec: BenchmarksDB.Data.Spec} = {
        name: 'benchmark-0', /** @todo */
        spec: undefined
    };

    async function startBenchmark(w: {dir: string, fn: string}, mode: {proof: ProofMode, simple: boolean} = {proof: ProofMode.INTERACTIVE, simple: false}) {
        var spec = bench.getSpec(w.dir, w.fn),
            docId = makeDocId(activeBenchmark.name, mode),
            doc = new MainDocument(docId, app.panes.proofTrace,
                                   OPTIONS[mode.proof]);
        doc.new();
        //app.hideBenchmarks();
        app.setActiveBenchmark({path: w});
        app.clear();
        app.setEditorText(BenchmarksDB.Data.unparseSpec(spec));
        app.add(doc);
        adjustParams(spec, mode);
        activeBenchmark.spec = spec;
        if (mode.proof !== ProofMode.AUTOMATIC)  // `startBenchmark` is a misnomer at this point... :/
            await doc.pi.start(spec, mode.proof);
    }

    /** @todo Pretty hideous duplication do refactor please */
    async function restartBenchmark(mode: {proof: ProofMode, simple: boolean} = {proof: ProofMode.INTERACTIVE, simple: false}) {
        var spec = BenchmarksDB.Data.parseSpec(activeBenchmark.name, app.getEditorText()),
            docId = makeDocId(activeBenchmark.name, mode),
            doc = new MainDocument(docId, app.panes.proofTrace,
                                   OPTIONS[mode.proof]);
        doc.new();
        app.clearMessages();
        app.add(doc);
        adjustParams(spec, mode);
        spec.spec.config = activeBenchmark.spec.spec.config;
        await doc.pi.start(spec, mode.proof);
    }

    function stopBenchmark() {
        app.doc.pi?.stop();
    }

    function makeDocId(name: string, mode: {proof: ProofMode, simple: boolean}) {
        return `${name}-${mode.proof}${mode.simple ? '-simple' : ''}`;
    }

    function adjustParams(spec: BenchmarksDB.Data.Spec, mode: {proof: ProofMode, simple: boolean}) {
        if (mode.simple)
            spec.params = ['--simple', 'true', ...(spec.params || [])];
    }

    async function switchMode(mode: {proof: ProofMode, simple: boolean}) {
        var docId = makeDocId(activeBenchmark.name, mode);
        if (app.has(docId))
            app.switchTo(docId);
        else
            restartBenchmark(mode);
    }

    function currentMode() {
        return {
            proof: app.options.auto ? ProofMode.AUTOMATIC : ProofMode.INTERACTIVE,
            simple: app.options.simple
        }
    }

    app.view.$watch(currentMode, switchMode);  /* neat ;) */

    const OPTIONS: {[mode: string]: MainDocument.Options} = {
        [ProofMode.AUTOMATIC]: {throttle: 750},
        [ProofMode.INTERACTIVE]: {expandImmediately: true}
    };

    app.on('benchmarks:action', w => startBenchmark(w, currentMode()));
    app.on('proofTrace:action', (action) => {
        switch (action.type) {
            case 'start':
            case 'restart': restartBenchmark(currentMode()); break;
            case 'stop': stopBenchmark(); break;
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
    var openOnStart = localStorage['openOnStart'];
    openOnStart = openOnStart ? JSON.parse(openOnStart) : DEFAULT_SCRATCH;
    if (openOnStart) {
        startBenchmark(openOnStart, currentMode());
    }

    Object.assign(window, {app, bench});
});