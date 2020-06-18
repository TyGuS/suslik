import $ from 'jquery';
import { ProofTrace } from './proof-trace';

        

$(async () => {
    var data = ProofTrace.Data.parse(await (await fetch('/trace.out')).text()),
        pt = new ProofTrace(data);

    $('#proof-trace-pane').append(pt.view.$el);

    Object.assign(window, {pt});
});