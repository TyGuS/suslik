import { readFileSync } from 'fs';
import $ from 'jquery';
import { ProofTrace } from './proof-trace';


const DATA = ProofTrace.Data.parse(readFileSync('trace.out', 'utf-8'));
        

$(() => {
    var pt = new ProofTrace(DATA);

    $('#proof-trace-pane').append(pt.view.$el);

    Object.assign(window, {pt});
});