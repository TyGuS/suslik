import $ from 'jquery';
import { MainDocument, DragDropJson } from './open';



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
    try {
        var pt = await doc.openRecent({silent: true});
        Object.assign(window, {pt});
    }
    catch (e) { console.error('open failed:', e); }

    var drop = new DragDropJson($('html'));
    drop.on('open', async ({file}) => {
        try {
            var pt = await doc.open(file);
            Object.assign(window, {pt});
        }
        catch (e) { }
    });

    Object.assign(window, {doc});
});