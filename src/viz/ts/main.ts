import $ from 'jquery';
import { MainDocument, DragDropJson } from './open';
import { ProofTrace } from './proof-trace';
import { ProofInteraction } from './proof-interaction';



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

    var pi = new ProofInteraction(doc.pt);
    pi.on('message', m => console.log('%cmessage', 'color: blue', m));
    pi.on('trace', u => {
        var data = ProofTrace.Data.fromEntries([u]);
        doc.pt.append(data);
    });
    pi.start();

    Object.assign(window, {doc, pi});
});