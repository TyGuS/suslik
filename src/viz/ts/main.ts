import $ from 'jquery';
import { MainDocument, DragDropJson } from './app';
import { ProofTrace } from './proof-trace';
import { ProofInteraction } from './proof-interaction';
import { BenchmarksDB } from './benchmarks';



declare var nw: any;

if (typeof nw !== 'undefined') {
    var win = nw.Window.get();
    win.zoomLevel = -2;
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

    /*
    var pi = new ProofInteraction(doc.pt);
    pi.on('message', m => console.log('%cmessage', 'color: blue', m));
    pi.start();
    */

    var spec = bench.getSpec('sll', 'free.syn');

    doc.on('benchmarks:action', async ev => {
        spec = bench.getSpec(ev.dir, ev.fn);
        doc.hideBenchmarks();
        await doc.pi.start();
        doc.pi.ws.send(JSON.stringify(spec));
        Object.assign(window, {spec});
    });

    Object.assign(window, {doc, bench, spec});
});