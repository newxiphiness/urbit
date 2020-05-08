import React from 'react';
import ReactDOM from 'react-dom';
import _ from 'lodash';
import { stringToTa } from '/lib/util';
import { store } from '/store';
import moment from 'moment';


class UrbitApi {
  setAuthTokens(authTokens) {
    this.authTokens = authTokens;
    this.bindPaths = [];

    this.bind = this.bind.bind(this);
  }

  bind(path, method, ship = this.authTokens.ship, app, success, fail, quit) {
    this.bindPaths = _.uniq([...this.bindPaths, path]);

    window.subscriptionId = window.urb.subscribe(ship, app, path,
      (err) => {
        fail(err);
      },
      (event) => {
        success({
          data: event,
          from: {
            ship,
            path
          }
        });
      },
      (qui) => {
        quit(qui);
      });
  }

  action(appl, mark, data) {
    return new Promise((resolve, reject) => {
      window.urb.poke(ship, appl, mark, data,
        (json) => {
          resolve(json);
        },
        (err) => {
          reject(err);
        });
    });
  }

  dbugAction(data) {
    return this.action("dbug", "dbug-action", data);
  }

  bindToVerb(app) {
    return this.bind('/verb/events', 'PUT', this.authTokens.ship, app,
      (result) => {
        console.log('verb result', result);
        result.data.app = app;
        store.handleEvent({data: { local: { verbResult: result.data }}});
      },
      () => {
        store.handleEvent({data: { local: { verbStatus: {
          app: app,
          msg: 'failed to establish verb connection to ' + app
        }}}});
      },
      () => {
        store.handleEvent({data: { local: { verbStatus: {
          app: app,
          msg: 'verb connection to ' + app + ' was dropped'
        }}}});
      }
    );
  }

  getJson(path, localTransform, onFail) {
    let source = '/~debug' + path + '.json';
    const query = window.location.href.split('?')[1];
    if (query) source = source + '?' + query;
    fetch(source)
    .then((response) => {
      if (!response.ok) {
        console.error('Network response not ok');
        onFail();
      } else {
        return response.json();
      }
    })
    .then((data) => {
      store.handleEvent({data: { local: localTransform(data) }});
    })
    .catch((error) => {
      console.error(`JSON fetch on ${source} failed:`, error);
      onFail();
    });
  }

  wrapLocal(name) {
    return (data) => {
      console.log('got data', data);
      let e = {};
      e[name] = data;
      e['status'] = null; // clear previous status
      return e;
    };
  }

  showStatus(what) {
    return () => {
      store.handleEvent({data: { local: { 'status': what }}});
    };
  }

  // apps

  getApps() {
    //TODO onfail render "failed to fetch apps"
    //TODO generic "fail" local event that prints to status bar?
    this.getJson('/app',
      this.wrapLocal('apps'),
      this.showStatus('error fetching apps')
    );
  }

  getAppDetails(app) {
    this.getJson('/app/'+app, (data) => {
        data.app = app;
        return this.wrapLocal('app')(data);
      },
      () => {  // on fail
        store.handleEvent({data: { local: { 'appFailed': app } }});
      }
    );
  }

  // spider

  getThreads() {
    console.log('getting threads');
    this.getJson('/spider/threads',
      this.wrapLocal('threads'),
      this.showStatus('error fetching threads')
    );
  }

  // ames

  getPeers() {
    this.getJson('/ames/peer',
      this.wrapLocal('amesPeers'),
      this.showStatus('error fetching ames peers')
    );
  }

  getPeer(who) {
    this.getJson(`/ames/peer/${who}`, (data) => {
        data.who = who;
        return this.wrapLocal('amesPeer')(data);
      },
      this.showStatus('error fetching ames details for ' + who)
    );
  }

  // behn

  getTimers() {
    this.getJson('/behn/timers',
      this.wrapLocal('behnTimers'),
      this.showStatus('error fetching behn timers')
    );
  }

  // clay

  getCommits() {
    this.getJson('/clay/commits',
      this.wrapLocal('clayCommits'),
      this.showStatus('error fetching clay commits')
    );
  }

  // eyre

  getBindings() {
    this.getJson('/eyre/bindings',
      this.wrapLocal('eyreBindings'),
      this.showStatus('error fetching eyre bindings')
    );
  }

  // local

  sidebarToggle() {
    let sidebarBoolean = true;
    if (store.state.sidebarShown === true) {
      sidebarBoolean = false;
    }
    store.handleEvent({
      data: {
        local: {
          'sidebarToggle': sidebarBoolean
        }
      }
    });
  }

}

export let api = new UrbitApi();
window.api = api;
