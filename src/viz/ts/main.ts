import $ from 'jquery';
import { ProofTrace } from './proof-trace';



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
    var data = ProofTrace.Data.parse(await (await fetch('/trace.out')).text()),
        pt = new ProofTrace(data);

    $('#proof-trace-pane').append(pt.view.$el);

    Object.assign(window, {pt});
});